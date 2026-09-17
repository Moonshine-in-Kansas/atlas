import Atlas.Conway.HSSideCount

noncomputable section
namespace Atlas.Conway
open Atlas.Codes Atlas.Lattices
attribute [local instance] Classical.propDecidable

abbrev HSPointLabels := {b : Mathieu23Points co3MarkedCoordinate // b ≠ co3BasePoint}
abbrev HSHexadLabels := {B : Co3Heptads co3MarkedCoordinate // co3BasePoint ∈ B.val}
abbrev HSWittVertices := Unit ⊕ (HSPointLabels ⊕ HSHexadLabels)

def hsWittLabel : HSWittVertices → Co3PointHeptad co3MarkedCoordinate
  | Sum.inl _ => Sum.inl co3BasePoint
  | Sum.inr (Sum.inl b) => Sum.inl b.val
  | Sum.inr (Sum.inr B) => Sum.inr B.val

theorem hsWittLabel_injective : Function.Injective hsWittLabel := by
  intro u v h
  cases u with
  | inl u =>
    cases v with
    | inl v => rfl
    | inr v =>
      cases v with
      | inl b => exact False.elim (b.prop (Sum.inl.inj h).symm)
      | inr B => cases h
  | inr u =>
    cases u with
    | inl b =>
      cases v with
      | inl v => exact False.elim (b.prop (Sum.inl.inj h))
      | inr v =>
        cases v with
        | inl c => exact congrArg (fun d : HSPointLabels => Sum.inr (Sum.inl d)) (Subtype.ext (Sum.inl.inj h))
        | inr C => cases h
    | inr B =>
      cases v with
      | inl v => cases h
      | inr v =>
        cases v with
        | inl c => cases h
        | inr C => exact congrArg (fun D : HSHexadLabels => Sum.inr (Sum.inr D)) (Subtype.ext (Sum.inr.inj h))

def hsWittVector : HSWittVertices → leech
  | Sum.inl _ => normSixVector co3MarkedCoordinate-minimumPairPlus co3MarkedCoordinate co3BasePoint.val
  | Sum.inr (Sum.inl b) => minimumPairPlus co3MarkedCoordinate b.val.val
  | Sum.inr (Sum.inr B) => normSixVector co3MarkedCoordinate-co3HeptadEndpoint co3MarkedCoordinate B.val

theorem hs_witt_pair (v : HSWittVertices) :
    ({hsWittVector v,normSixVector co3MarkedCoordinate-hsWittVector v} : Finset leech) =
      (co3PointHeptadDecompositionEquiv co3MarkedCoordinate (hsWittLabel v)).val := by
  cases v with
  | inl v =>
    change {_,normSixVector _-(normSixVector _-minimumPairPlus _ _)} =
      {(co3EvenEndpointMap _ (Sum.inl co3BasePoint)).val,_}
    rw [sub_sub_cancel,Finset.pair_comm]
    rfl
  | inr v =>
    cases v with
    | inl b => rfl
    | inr B =>
      change {_,normSixVector _-(normSixVector _-co3HeptadEndpoint _ _)} =
        {co3HeptadEndpoint _ _,_}
      rw [sub_sub_cancel,Finset.pair_comm]
      rfl

theorem hs_witt_vector_norms (v : HSWittVertices) :
    integerDot (hsWittVector v).val (hsWittVector v).val = 32 ∧
      integerDot (normSixVector co3MarkedCoordinate).val (hsWittVector v).val = 24 := by
  have he := (co3EvenEndpointMap co3MarkedCoordinate (hsWittLabel v)).prop
  have hn : integerDot (hsWittVector v).val (hsWittVector v).val = 32 ∧
      integerDot (normSixVector co3MarkedCoordinate-hsWittVector v).val
        (normSixVector co3MarkedCoordinate-hsWittVector v).val = 32 := by
    cases v with
    | inl v =>
      simp only [hsWittVector]
      change integerDot (normSixVector _-minimumPairPlus _ _).val _ = 32 ∧ _
      rw [sub_sub_cancel]
      exact ⟨he.2.1,he.1⟩
    | inr v =>
      cases v with
      | inl b => exact ⟨he.1,he.2.1⟩
      | inr B =>
        simp only [hsWittVector]
        change integerDot (normSixVector _-co3HeptadEndpoint _ _).val _ = 32 ∧ _
        rw [sub_sub_cancel]
        exact ⟨he.2.1,he.1⟩
  exact ⟨hn.1,normSix_decomposition_dot _ _ hn.1 hn.2⟩

theorem hs_witt_vector_pairing (v : HSWittVertices) :
    integerDot hsEndpoint.val (hsWittVector v).val = 16 := by
  change integerDot (minimumPairMinus _ _).val _ = 16
  rw [minimumPairMinus_dot]
  cases v with
  | inl v =>
    change 4*((normSixVector _-minimumPairPlus _ _).val co3MarkedCoordinate-
      (normSixVector _-minimumPairPlus _ _).val co3BasePoint.val)=16
    simp [normSixVector_apply,minimumPairPlus,coordinateVector,Pi.single_apply,
      co3MarkedCoordinate,co3BasePoint]
  | inr v =>
    cases v with
    | inl b =>
      have hba : b.val.val ≠ co3MarkedCoordinate := b.val.prop
      have hbp : b.val.val ≠ co3BasePoint.val := fun h => b.prop (Subtype.ext h)
      change 4*((minimumPairPlus _ _).val _-(minimumPairPlus _ _).val _)=16
      simp [minimumPairPlus,coordinateVector,Pi.single_apply,hba,hbp,Ne.symm hba,
        Ne.symm hbp,show co3MarkedCoordinate ≠ co3BasePoint.val from Ne.symm co3BasePoint.prop,
        show co3BasePoint.val ≠ co3MarkedCoordinate from co3BasePoint.prop]
    | inr B =>
      change 4*(((normSixVector _).val co3MarkedCoordinate-(co3HeptadEndpoint _ B.val).val co3MarkedCoordinate)-
        ((normSixVector _).val co3BasePoint.val-(co3HeptadEndpoint _ B.val).val co3BasePoint.val))=16
      rw [co3HeptadEndpoint_marked,co3HeptadEndpoint_other]
      simp [normSixVector_apply,B.prop,show co3BasePoint.val ≠ co3MarkedCoordinate from co3BasePoint.prop]

def hsWittGraphMap (v : HSWittVertices) : HSGraphPoints :=
  ⟨hsWittVector v,(hs_witt_vector_norms v).1,(hs_witt_vector_norms v).2,hs_witt_vector_pairing v⟩

theorem hsWittGraphMap_injective : Function.Injective hsWittGraphMap := by
  intro u v h
  have he : hsWittVector u = hsWittVector v := congrArg Subtype.val h
  have hp := hs_witt_pair u
  rw [he,hs_witt_pair v] at hp
  apply hsWittLabel_injective
  exact (co3PointHeptadDecompositionEquiv _).injective (Subtype.ext hp.symm)

end Atlas.Conway
