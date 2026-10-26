import Atlas.Rudvalis.HeavySeedLifts
import Atlas.Rudvalis.HeavySupportOrbit

namespace Atlas.Rudvalis
open Atlas.Codes.Quaternary

theorem minimumLift_card_binary_transport (p : binaryPermutationGroup) (d : BinaryWord)
    (hd : hammingNorm d=16) :
    Nat.card (minimumLift (d ∘ p.val.symm))=Nat.card (minimumLift d) := by
  have hp : hammingNorm (d ∘ p.val.symm)=16 := (binaryWord_weight_permute d p.val.symm).trans hd
  rw [Nat.card_congr (minimumSignedLiftEquiv _ hp),Nat.card_congr (minimumSignedLiftEquiv _ hd)]
  obtain ⟨g,hg⟩ := codePermutationHom_surjective p
  have he : g.val.right=p.val := congrArg Subtype.val hg
  rw [← he]
  exact (signedLift_card_transport g d).symm

theorem heavy_minimum_fibre_card (d : BinaryWord) (hh : hasNonzeroQuadraticPart d)
    (hw : hammingNorm d=16) : Nat.card (minimumLift d)=16 := by
  obtain ⟨a,hc,ha⟩ := hh
  obtain ⟨p,hp⟩ := heavySupport_seed_orbit a.1 a.2.1 a.2.2 hc (ha ▸ hw)
  have he : d=heavySeedResidue ∘ p.val := ha.symm.trans hp
  rw [he]
  have h := minimumLift_card_binary_transport p⁻¹ heavySeedResidue heavySeedResidue_weight
  exact h.trans heavySeed_minimum_lifts_card

abbrev HeavyMinimumWords := {w : quaternaryCode //
  euclideanWeight w.val=16 ∧ hasNonzeroQuadraticPart (reduce w.val)}
abbrev HeavyMinimumResidues := {d : binaryResidue //
  hasNonzeroQuadraticPart d.val ∧ hammingNorm d.val=16}

noncomputable def heavyMinimumWordsEquiv :
    HeavyMinimumWords ≃ Σ d : HeavyMinimumResidues,minimumLift d.val.val where
  toFun w := ⟨⟨⟨reduce w.val.val,(quaternaryCode_residue _).mpr ⟨_,w.val.prop,rfl⟩⟩,
    w.prop.2,quaternary_minimum_residue_weight _ w.val.prop w.prop.1⟩,⟨w.val,w.prop.1,rfl⟩⟩
  invFun w := ⟨w.2.val,w.2.prop.1,by rw [w.2.prop.2]; exact w.1.prop.1⟩
  left_inv _ := Subtype.ext rfl
  right_inv w := by
    rcases w with ⟨⟨⟨d,hd⟩,hheavy,hweight⟩,⟨⟨v,hv⟩,hw,hr⟩⟩
    dsimp at hr
    subst d
    rfl

theorem heavy_minimum_words_card : Nat.card HeavyMinimumWords=14336 := by
  classical
  rw [Nat.card_congr heavyMinimumWordsEquiv,Nat.card_sigma]
  have he (d : HeavyMinimumResidues) : Nat.card (minimumLift d.val.val)=16 :=
    heavy_minimum_fibre_card _ d.prop.1 d.prop.2
  simp_rw [he]
  simp only [Finset.sum_const,Finset.card_univ,smul_eq_mul]
  rw [← Nat.card_eq_fintype_card]
  change Nat.card {d : binaryResidue // hasNonzeroQuadraticPart d.val ∧ hammingNorm d.val=16}*16=14336
  rw [binaryQuadratic_weight_sixteen_count]

end Atlas.Rudvalis
