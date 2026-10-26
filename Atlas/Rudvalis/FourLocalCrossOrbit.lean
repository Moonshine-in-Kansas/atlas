import Atlas.Rudvalis.FourLocalTransitivity

namespace Atlas.Rudvalis
open Atlas.Codes.Quaternary

theorem fourLocal_shell_transitive (v w : fourShellPiece)
    (hv : CrossOrthogonal (coordinateCross (rowLabel 0,0)) (minimalCross v.val))
    (hw : CrossOrthogonal (coordinateCross (rowLabel 0,0)) (minimalCross w.val)) :
    ∃g : codeGroup,g • coordinateCross (rowLabel 0,0)=coordinateCross (rowLabel 0,0) ∧ g • v.val=w.val := by
  obtain ⟨a,ha⟩ := v.prop
  obtain ⟨b,hb⟩ := w.prop
  rw [←ha] at hv
  rw [←hb] at hw
  have hav := (fourWord_coordinate_orthogonal_iff a (rowLabel 0) 0).mp hv
  have hbw := (fourWord_coordinate_orthogonal_iff b (rowLabel 0) 0).mp hw
  obtain ⟨g,hg⟩ := fourLocal_minimum_words_transitive a.val.val b.val.val a.val.prop b.val.prop
    a.prop.1 b.prop.1 a.prop.2 b.prop.2 hav hbw
  refine ⟨g.val,?_,?_⟩
  · have hf := g.prop
    change g.val • coordinateCross (originalCoordinateEquiv (0,1))=coordinateCross (originalCoordinateEquiv (0,1)) at hf
    rwa [(originalCoordinate_pair 0).1] at hf
  · rw [←ha,←hb,←minimumWordShellLift_equivariant]
    apply congrArg minimumWordShellLift
    exact Subtype.ext (Subtype.ext hg)

/-- Actual transitivity on the 192 four-block crosses orthogonal to the reference cross. -/
theorem fourLocal_crosses_transitive (v w : FourBlockCrosses)
    (hv : CrossOrthogonal (coordinateCross (rowLabel 0,0)) (shellPieceCrossMap fourShellPiece v))
    (hw : CrossOrthogonal (coordinateCross (rowLabel 0,0)) (shellPieceCrossMap fourShellPiece w)) :
    ∃g : codeGroup,g • coordinateCross (rowLabel 0,0)=coordinateCross (rowLabel 0,0) ∧
      g • shellPieceCrossMap fourShellPiece v=shellPieceCrossMap fourShellPiece w := by
  induction v using Quotient.inductionOn with | h v =>
    induction w using Quotient.inductionOn with | h w =>
      obtain ⟨g,hfix,hg⟩ := fourLocal_shell_transitive v w hv hw
      refine ⟨g,hfix,?_⟩
      change g • minimalCross v.val=minimalCross w.val
      rw [←minimalCross_smul,hg]

end Atlas.Rudvalis
