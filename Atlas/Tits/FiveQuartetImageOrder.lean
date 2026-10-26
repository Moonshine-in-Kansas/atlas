import Atlas.Tits.FiveQuartetBeta
import Atlas.GroupTheory.FivePointImageOrder

namespace Atlas.Tits

instance fiveQuartetsFinite : Finite FiveQuartets :=
  (Nat.card_pos_iff.mp (cardFiveQuartets ▸ (by decide : 0 < 5))).2

noncomputable instance fiveQuartetImageTransitive :
    MulAction.IsPretransitive fiveQuartetImage FiveQuartets where
  exists_smul_eq Q R := by
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq pairStabilizer Q R
    exact ⟨⟨fiveQuartetHom g, ⟨g,rfl⟩⟩, hg⟩

theorem fiveQuartetImage_card_dvd : Nat.card fiveQuartetImage ∣ 20480 := by
  have h := Subgroup.card_dvd_of_surjective fiveQuartetHom.rangeRestrict
    fiveQuartetHom.rangeRestrict_surjective
  exact cardPairStabilizer ▸ h

noncomputable def imageBeta : fiveQuartetImage := ⟨fiveQuartetBeta, ⟨pairBeta, rfl⟩⟩

theorem imageBeta_order : orderOf imageBeta = 4 := by
  rw [← orderOf_injective fiveQuartetImage.subtype Subtype.val_injective imageBeta]
  exact fiveQuartetBeta_order

/-- Order of the image of the actual pair-stabilizer action on its five quartets. -/
theorem fiveQuartetImage_order : Nat.card fiveQuartetImage = 20 :=
  Atlas.GroupTheory.card_twenty_of_faithful_five_point_action cardFiveQuartets
    fiveQuartetImage_card_dvd imageBeta imageBeta_order

end Atlas.Tits
