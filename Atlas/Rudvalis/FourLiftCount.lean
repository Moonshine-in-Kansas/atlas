import Atlas.Rudvalis.FourSupportOrbit
import Atlas.Rudvalis.FourSeedLifts

namespace Atlas.Rudvalis
open Atlas.Codes.Quaternary

theorem fourPlaneSeedResidue_normal : fourPlaneSeedResidue=
    binaryNormalMap ((seedEncodedParameters 149).1,outerMatrix (binaryLabel 1) (binaryLabel 1),0) := by
  rw [fourPlaneSeedResidue_parameters]
  congr 1
  apply Prod.ext
  · rfl
  · decide +kernel

theorem fourSupport_seed_orbit (d : BinaryWord) (hd : admissibleFourSupport d) :
    ∃ g : binaryPermutationGroup,d=fourPlaneSeedResidue ∘ g.val := by
  have w : minimumLift (binaryNormalMap
      ((seedEncodedParameters 149).1,outerMatrix (binaryLabel 1) (binaryLabel 1),0)) := by
    rw [← fourPlaneSeedResidue_normal]
    exact fourPlaneSeedMinimumLift
  rw [fourPlaneSeedResidue_normal]
  exact fourSupport_from_base_orbit _ w d hd

theorem admissibleFourSupport_weight (d : BinaryWord) (hd : admissibleFourSupport d) :
    hammingNorm d=16 := by
  obtain ⟨g,hg⟩ := fourSupport_seed_orbit d hd
  rw [hg,binaryWord_weight_permute,fourPlaneSeedResidue_weight]

theorem four_minimum_fibre_card (d : BinaryWord) (hd : admissibleFourSupport d) :
    Nat.card (minimumLift d)=32 := by
  obtain ⟨g,hg⟩ := fourSupport_seed_orbit d hd
  rw [hg]
  exact (minimumLift_card_binary_transport g⁻¹ fourPlaneSeedResidue fourPlaneSeedResidue_weight).trans
    fourPlaneSeed_minimum_lifts_card

abbrev FourMinimumWords := {w : quaternaryCode //
  euclideanWeight w.val=16 ∧ admissibleFourSupport (reduce w.val)}

noncomputable def fourMinimumWordsEquiv :
    FourMinimumWords ≃ Σ d : {d : BinaryWord // admissibleFourSupport d},minimumLift d.val where
  toFun w := ⟨⟨reduce w.val.val,w.prop.2⟩,⟨w.val,w.prop.1,rfl⟩⟩
  invFun w := ⟨w.2.val,w.2.prop.1,by rw [w.2.prop.2]; exact w.1.prop⟩
  left_inv _ := Subtype.ext rfl
  right_inv w := by
    rcases w with ⟨⟨d,hd⟩,⟨⟨v,hv⟩,hw,hr⟩⟩
    dsimp at hr
    subst d
    rfl

theorem four_minimum_words_card : Nat.card FourMinimumWords=1792 := by
  classical
  rw [Nat.card_congr fourMinimumWordsEquiv,Nat.card_sigma]
  simp_rw [four_minimum_fibre_card _ (Subtype.prop _)]
  simp only [Finset.sum_const,Finset.card_univ,smul_eq_mul]
  rw [← Nat.card_eq_fintype_card,admissibleFourSupport_count]

end Atlas.Rudvalis
