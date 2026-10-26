import Atlas.Codes.QuaternaryLiftFibres
import Atlas.Rudvalis.CodeGroupOrder

/-! Actual minimum-word fibres and their shortened-torsion cardinalities. -/
namespace Atlas.Rudvalis
open Atlas.Codes.Quaternary

abbrev torsionOn (d : BinaryWord) := supportedCode binaryTorsion d
abbrev minimumLift (d : BinaryWord) :=
  {w : quaternaryCode // euclideanWeight w.val=16 ∧ reduce w.val=d}

noncomputable def minimumSignedLiftEquiv (d : BinaryWord) (hd : hammingNorm d=16) :
    minimumLift d ≃ SignedLift quaternaryCode d :=
  Equiv.subtypeEquivRight (fun w => by
    constructor
    · rintro ⟨hweight,hr⟩
      exact ⟨hr,quaternary_minimum_no_twos w.val w.prop hweight⟩
    · rintro ⟨hr,hn⟩
      refine ⟨?_,hr⟩
      rw [(euclideanWeight_eq_residue_iff w.val).mpr hn,hr,hd])

theorem minimumLift_card (d : BinaryWord) (hd : hammingNorm d=16) (w : minimumLift d) :
    Nat.card (minimumLift d)=Nat.card (torsionOn d) := by
  let e := minimumSignedLiftEquiv d hd
  exact (Nat.card_congr e).trans (Nat.card_congr
    (signedLiftEquiv quaternaryCode binaryTorsion quaternaryCode_torsion d (e w))).symm

theorem monomial_no_twos (g : SignedCoordinates Coordinate) (w : QuaternaryWord)
    (hw : ∀ z,w z≠2) : ∀ z,monomialHom g w z≠2 := by
  have h : ∀ a : Quat,∀ b : Binary,a≠2 → signedScalar b a≠2 := by decide +kernel
  intro z
  exact h _ _ (hw (g.right.symm z))

noncomputable def signedLiftAction (g : codeGroup) (d : BinaryWord) :
    SignedLift quaternaryCode d → SignedLift quaternaryCode (d ∘ g.val.right.symm) := fun w =>
  ⟨⟨monomialHom g.val w.val.val,(g.prop _).mp w.val.prop⟩,
    by
      change reduce (monomialAction g.val w.val.val)=_
      rw [monomialAction_reduce,w.prop.1],monomial_no_twos g.val w.val.val w.prop.2⟩

theorem signedLift_nonempty_of_binary_transport (p : binaryPermutationGroup) (d : BinaryWord)
    (w : SignedLift quaternaryCode d) :
    Nonempty (SignedLift quaternaryCode (d ∘ p.val.symm)) := by
  obtain ⟨g,hg⟩ := codePermutationHom_surjective p
  have he : g.val.right=p.val := congrArg Subtype.val hg
  exact he ▸ ⟨signedLiftAction g d w⟩

noncomputable def signedLiftActionEquiv (g : codeGroup) (d : BinaryWord) :
    SignedLift quaternaryCode d ≃ SignedLift quaternaryCode (d ∘ g.val.right.symm) where
  toFun := signedLiftAction g d
  invFun w := ⟨⟨monomialHom g.val⁻¹ w.val.val,(g⁻¹).prop _ |>.mp w.val.prop⟩,
    by
      change reduce (monomialAction g.val⁻¹ w.val.val)=d
      rw [monomialAction_reduce,w.prop.1]
      funext i
      exact congrArg d (g.val.right.symm_apply_apply i),
    monomial_no_twos g.val⁻¹ w.val.val w.prop.2⟩
  left_inv w := by
    apply Subtype.ext
    apply Subtype.ext
    change monomialHom g.val⁻¹ (monomialHom g.val w.val.val)=w.val.val
    simp
  right_inv w := by
    apply Subtype.ext
    apply Subtype.ext
    change monomialHom g.val (monomialHom g.val⁻¹ w.val.val)=w.val.val
    simp

theorem signedLift_card_transport (g : codeGroup) (d : BinaryWord) :
    Nat.card (SignedLift quaternaryCode d)=
      Nat.card (SignedLift quaternaryCode (d ∘ g.val.right.symm)) :=
  Nat.card_congr (signedLiftActionEquiv g d)

end Atlas.Rudvalis
