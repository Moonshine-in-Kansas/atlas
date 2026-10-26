import Atlas.LinearGroups.F4.ParabolicOppositeDecomposition
import Atlas.LinearGroups.F4.OppositeCrossMarked

/-! The two opposite marked vectors have inverse scales under the actual
opposite-pair subgroup. -/
noncomputable section
namespace Atlas.F4
open Atlas.Albert
variable {F : Type*} [Field F]

theorem oppositeBaseCell_eq_pairOpposite :
    (oppositeBaseCell (F:=F)).val=pairOppositeVector := oppositeBaseCell_coordinates

theorem pairStabilizer_positive_scale (g : oppositePairStabilizer (F:=F)) :
    g.val.val.val parabolicVector=(parabolicLineCharacter g.val).val • parabolicVector :=
  parabolicLineCharacter_action g.val

theorem pairStabilizer_opposite_scale (g : oppositePairStabilizer (F:=F)) :
    g.val.val.val pairOppositeVector=((parabolicLineCharacter g.val)⁻¹).val • pairOppositeVector := by
  have h := congrArg Subtype.val g.prop
  change (g.val • oppositeBaseCell).val=(oppositeBaseCell (F:=F)).val at h
  rw [oppositeCellParabolicAction_val,oppositeBaseCell_eq_pairOpposite] at h
  have hh := congrArg (fun x : Carrier F => ((parabolicLineCharacter g.val)⁻¹).val • x) h
  simpa only [smul_smul,Units.inv_mul,one_smul] using hh

end Atlas.F4
