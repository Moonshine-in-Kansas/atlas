import Atlas.Rudvalis.FourRowKernelFibre
import Atlas.Rudvalis.FourCoupleProjection

namespace Atlas.Rudvalis
open Atlas.Codes.Quaternary
open scoped BigOperators
open Classical

/-- Intrinsic label of a four-block cross, read from its orthogonality to coordinate rows. -/
def FourCrossHasLabel (a : Point) (c : MinimalCross) : Prop :=
  ∀p : Point,∀x : E,CrossOrthogonal (coordinateCross (p,x)) c ↔ dot a.val p.val=0

 theorem fourWord_row_orthogonal_normal (w : FourMinimumWords) (p : Point) (x : E) :
    CrossOrthogonal (coordinateCross (p,x)) (minimalCross (minimumWordShellLift (fourMinimumWord w))) ↔
      dot (fourSupportNormal ⟨reduce w.val.val,w.prop.2⟩).val p.val=0 := by
  rw [fourWord_coordinate_orthogonal_iff]
  let d : {d : BinaryWord // admissibleFourSupport d} := ⟨reduce w.val.val,w.prop.2⟩
  have h := fourSupport_parameter_row_zero (fourSupportEquiv.symm d) p
  simpa only [Equiv.apply_symm_apply,d,fourSupportNormal] using h

 theorem fourWord_label_iff (a : Point) (w : FourMinimumWords) :
    FourCrossHasLabel a (minimalCross (minimumWordShellLift (fourMinimumWord w))) ↔
      fourSupportNormal ⟨reduce w.val.val,w.prop.2⟩=a := by
  have hu : ∀a b : Point,(∀p : Point,dot a.val p.val=0 ↔ dot b.val p.val=0) ↔ a=b := by
    decide +kernel
  constructor
  · intro h
    apply (hu _ a).mp
    intro p
    exact (fourWord_row_orthogonal_normal w p 0).symm.trans (h p 0)
  · intro h p x
    rw [fourWord_row_orthogonal_normal,h]

abbrev FourLabelSupports (a : Point) :=
  {d : {d : BinaryWord // admissibleFourSupport d} // fourSupportNormal d=a}
abbrev FourLabelWords (a : Point) :=
  {w : FourMinimumWords // fourSupportNormal ⟨reduce w.val.val,w.prop.2⟩=a}

noncomputable def fourLabelSupportsEquiv (a : Point) :
    FourLabelSupports a ≃ Σb : {b : Point // b=a},OddActiveConstants b.val :=
  (Equiv.subtypeEquiv fourSupportEquiv (fun v=>by simp only [fourSupportNormal,Equiv.symm_apply_apply])).symm.trans
    (Equiv.subtypeSigmaEquiv OddActiveConstants (fun b=>b=a))

 theorem fourLabelSupports_card (a : Point) : Nat.card (FourLabelSupports a)=8 := by
  rw [Nat.card_congr (fourLabelSupportsEquiv a),Nat.card_sigma]
  simp_rw [oddActiveConstants_card]
  simp

noncomputable def fourLabelWordsEquiv (a : Point) :
    FourLabelWords a ≃ Σd : FourLabelSupports a,minimumLift d.val.val :=
  (Equiv.subtypeEquiv fourMinimumWordsEquiv (fun _=>Iff.rfl)).trans
    (Equiv.subtypeSigmaEquiv (fun d : {d : BinaryWord // admissibleFourSupport d}=>minimumLift d.val)
      (fun d=>fourSupportNormal d=a))

 theorem fourLabelWords_card (a : Point) : Nat.card (FourLabelWords a)=256 := by
  rw [Nat.card_congr (fourLabelWordsEquiv a),Nat.card_sigma]
  simp_rw [four_minimum_fibre_card _ (Subtype.prop _)]
  simp only [Finset.sum_const,Finset.card_univ,smul_eq_mul]
  rw [←Nat.card_eq_fintype_card,fourLabelSupports_card]

noncomputable def fourLabelShellEquiv (a : Point) :
    FourLabelWords a ≃ RestrictedShellPiece fourShellPiece (FourCrossHasLabel a) :=
  Equiv.subtypeEquiv fourWordShellEquiv (fun w=>(fourWord_label_iff a w).symm)

 theorem fourLabelCrosses_card (a : Point) :
    Nat.card {c : FourBlockCrosses // FourCrossHasLabel a (shellPieceCrossMap fourShellPiece c)}=64 := by
  have h := restricted_shell_cross_card fourShellPiece (FourCrossHasLabel a)
  rw [←Nat.card_congr (fourLabelShellEquiv a),fourLabelWords_card] at h
  have hh : 256=Nat.card {c : FourBlockCrosses // FourCrossHasLabel a (shellPieceCrossMap fourShellPiece c)}*4 := h
  omega

end Atlas.Rudvalis
