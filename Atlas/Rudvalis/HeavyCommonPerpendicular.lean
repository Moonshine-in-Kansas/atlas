import Atlas.Rudvalis.HeavyCoupleSupports
import Atlas.Rudvalis.CoordinateCommonPerpendicular

/-! The 512 heavy crosses perpendicular to the reference coordinate couple. -/
namespace Atlas.Rudvalis
open scoped BigOperators
open Atlas.Codes.Quaternary

def HeavyCoupleZero (d : BinaryWord) : Prop :=
  (d (rowLabel 0,0)=0 ∧ d (rowLabel 0,0+(rowLabel 0).val)=0) ∧
  (d (rowLabel 0,binaryLabel 2)=0 ∧ d (rowLabel 0,binaryLabel 2+(rowLabel 0).val)=0)

abbrev HeavyCoupleResidues := {d : HeavyMinimumResidues // HeavyCoupleZero d.val.val}

noncomputable def heavyCoupleResidueEquiv : HeavyCoupleParameters ≃ HeavyCoupleResidues :=
  (show HeavyCoupleParameters ≃
    {a : QuadraticMinimumParameters // HeavyCoupleZero (fixedHeavyWord a.1 a.2)} from
    {toFun := fun z => ⟨⟨z.1,z.2.val.val⟩,z.2.val.prop,z.2.prop⟩
     invFun := fun a => ⟨a.val.1,⟨⟨a.val.2,a.prop.1⟩,a.prop.2⟩⟩
     left_inv := fun _ => rfl
     right_inv := fun _ => rfl}).trans
    (Equiv.subtypeEquiv quadraticMinimumWordEquiv (fun _ => Iff.rfl))

theorem heavyCoupleResidues_card : Nat.card HeavyCoupleResidues=128 := by
  rw [←Nat.card_congr heavyCoupleResidueEquiv,heavyCoupleParameters_card]

abbrev HeavyCoupleWords := {w : HeavyMinimumWords // HeavyCoupleZero (reduce w.val.val)}

noncomputable def heavyCoupleWordsEquiv :
    HeavyCoupleWords ≃ Σ d : HeavyCoupleResidues,minimumLift d.val.val.val :=
  (Equiv.subtypeEquiv heavyMinimumWordsEquiv (fun _ => Iff.rfl)).trans
    (Equiv.subtypeSigmaEquiv (fun d : HeavyMinimumResidues => minimumLift d.val.val)
      (fun d => HeavyCoupleZero d.val.val))

theorem heavyCoupleWords_card : Nat.card HeavyCoupleWords=2048 := by
  classical
  rw [Nat.card_congr heavyCoupleWordsEquiv,Nat.card_sigma]
  have hh (d : HeavyCoupleResidues) : Nat.card (minimumLift d.val.val.val)=16 :=
    heavy_minimum_fibre_card _ d.val.prop.1 d.val.prop.2
  simp_rw [hh]
  simp only [Finset.sum_const,Finset.card_univ,smul_eq_mul]
  rw [←Nat.card_eq_fintype_card,heavyCoupleResidues_card]

def ReferenceCoupleOrthogonal (c : MinimalCross) : Prop :=
  CrossOrthogonal localReferenceCross c ∧ CrossOrthogonal referenceSecondCross c

theorem heavyWord_reference_couple_iff (w : HeavyMinimumWords) :
    ReferenceCoupleOrthogonal (minimalCross (minimumWordShellLift (heavyMinimumWord w))) ↔
      HeavyCoupleZero (reduce w.val.val) := by
  rw [ReferenceCoupleOrthogonal,localReferenceCross_eq,referenceSecondCross_eq,
    heavyWord_coordinate_orthogonal_iff,heavyWord_coordinate_orthogonal_iff]
  rfl

noncomputable def heavyCoupleShellEquiv :
    HeavyCoupleWords ≃ RestrictedShellPiece heavyShellPiece ReferenceCoupleOrthogonal :=
  Equiv.subtypeEquiv heavyWordShellEquiv (fun w => (heavyWord_reference_couple_iff w).symm)

theorem heavyCoupleShell_card :
    Nat.card (RestrictedShellPiece heavyShellPiece ReferenceCoupleOrthogonal)=2048 := by
  rw [←Nat.card_congr heavyCoupleShellEquiv,heavyCoupleWords_card]

theorem heavyCommonPerpendicularCrosses_card :
    Nat.card {c : HeavyCrosses //
      CrossOrthogonal localReferenceCross (shellPieceCrossMap heavyShellPiece c) ∧
      CrossOrthogonal referenceSecondCross (shellPieceCrossMap heavyShellPiece c)}=512 := by
  have h := restricted_shell_cross_card heavyShellPiece ReferenceCoupleOrthogonal
  rw [heavyCoupleShell_card] at h
  change 2048=Nat.card {c : HeavyCrosses //
    CrossOrthogonal localReferenceCross (shellPieceCrossMap heavyShellPiece c) ∧
    CrossOrthogonal referenceSecondCross (shellPieceCrossMap heavyShellPiece c)}*4 at h
  omega

end Atlas.Rudvalis
