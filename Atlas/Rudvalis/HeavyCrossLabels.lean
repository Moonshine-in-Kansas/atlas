import Atlas.Rudvalis.HeavyBlockTransport

namespace Atlas.Rudvalis
open Atlas.Codes.Quaternary
open scoped BigOperators
open Classical

noncomputable def heavyResidueLabel (d : HeavyMinimumResidues) : Point :=
  (quadraticMinimumWordEquiv.symm d).1

noncomputable def heavyWordLabel (w : HeavyMinimumWords) : Point :=
  heavyResidueLabel (heavyMinimumWordsEquiv w).1

def HeavyCrossHasLabel (p : Point) (c : MinimalCross) : Prop :=
  ∀x : E,¬CrossOrthogonal (coordinateCross (p,x)) c

theorem heavyWord_parameters (w : HeavyMinimumWords) :
    ∃v : FixedHeavyParameters (heavyWordLabel w),
      reduce w.val.val=fixedHeavyWord (heavyWordLabel w) v := by
  refine ⟨(quadraticMinimumWordEquiv.symm (heavyMinimumWordsEquiv w).1).2,?_⟩
  exact (congrArg (fun d : HeavyMinimumResidues=>d.val.val)
    (quadraticMinimumWordEquiv.apply_symm_apply (heavyMinimumWordsEquiv w).1)).symm

theorem heavyWord_label_iff (p : Point) (w : HeavyMinimumWords) :
    HeavyCrossHasLabel p (minimalCross (minimumWordShellLift (heavyMinimumWord w))) ↔
      heavyWordLabel w=p := by
  obtain ⟨v,hv⟩ := heavyWord_parameters w
  have h := fixedHeavy_row_pairs_card (heavyWordLabel w) p v
  have he : HeavyCrossHasLabel p (minimalCross (minimumWordShellLift (heavyMinimumWord w))) ↔
      (Finset.univ.filter (fun x : E=>fixedHeavyWord (heavyWordLabel w) v (p,x)=0 ∧
        fixedHeavyWord (heavyWordLabel w) v (p,x+p.val)=0)).card=0 := by
    simp only [HeavyCrossHasLabel,heavyWord_coordinate_orthogonal_iff,hv,
      Finset.card_eq_zero,Finset.filter_eq_empty_iff,Finset.mem_univ,true_implies]
  rw [he,h]
  by_cases hp : p=heavyWordLabel w <;> simp [hp,eq_comm]

abbrev HeavyLabelResidues (p : Point) := {d : HeavyMinimumResidues // heavyResidueLabel d=p}
abbrev HeavyLabelWords (p : Point) := {w : HeavyMinimumWords // heavyWordLabel w=p}

noncomputable def heavyLabelResiduesEquiv (p : Point) :
    HeavyLabelResidues p ≃ Σc : {c : Point // c=p},FixedHeavyParameters c.val :=
  (Equiv.subtypeEquiv quadraticMinimumWordEquiv (fun v=>by
    simp only [heavyResidueLabel,Equiv.symm_apply_apply])).symm.trans
    (Equiv.subtypeSigmaEquiv FixedHeavyParameters (fun c=>c=p))

theorem heavyLabelResidues_card (p : Point) : Nat.card (HeavyLabelResidues p)=128 := by
  rw [Nat.card_congr (heavyLabelResiduesEquiv p),Nat.card_sigma]
  simp_rw [fixedHeavyParameters_card]
  simp

noncomputable def heavyLabelWordsEquiv (p : Point) :
    HeavyLabelWords p ≃ Σd : HeavyLabelResidues p,minimumLift d.val.val.val :=
  (Equiv.subtypeEquiv heavyMinimumWordsEquiv (fun _=>Iff.rfl)).trans
    (Equiv.subtypeSigmaEquiv (fun d : HeavyMinimumResidues=>minimumLift d.val.val)
      (fun d=>heavyResidueLabel d=p))

theorem heavyLabelWords_card (p : Point) : Nat.card (HeavyLabelWords p)=2048 := by
  rw [Nat.card_congr (heavyLabelWordsEquiv p),Nat.card_sigma]
  have h (d : HeavyLabelResidues p) : Nat.card (minimumLift d.val.val.val)=16 :=
    heavy_minimum_fibre_card _ d.val.prop.1 d.val.prop.2
  simp_rw [h]
  simp only [Finset.sum_const,Finset.card_univ,smul_eq_mul]
  rw [←Nat.card_eq_fintype_card,heavyLabelResidues_card]

noncomputable def heavyLabelShellEquiv (p : Point) :
    HeavyLabelWords p ≃ RestrictedShellPiece heavyShellPiece (HeavyCrossHasLabel p) :=
  Equiv.subtypeEquiv heavyWordShellEquiv (fun w=>(heavyWord_label_iff p w).symm)

theorem heavyLabelCrosses_card (p : Point) :
    Nat.card {c : HeavyCrosses // HeavyCrossHasLabel p (shellPieceCrossMap heavyShellPiece c)}=512 := by
  have h := restricted_shell_cross_card heavyShellPiece (HeavyCrossHasLabel p)
  rw [←Nat.card_congr (heavyLabelShellEquiv p),heavyLabelWords_card] at h
  change 2048=Nat.card {c : HeavyCrosses // HeavyCrossHasLabel p (shellPieceCrossMap heavyShellPiece c)}*4 at h
  omega

end Atlas.Rudvalis
