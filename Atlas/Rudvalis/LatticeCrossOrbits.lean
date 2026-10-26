import Atlas.Rudvalis.LatticeCrossPieces
import Atlas.Rudvalis.HeavyMinimumOrbit

namespace Atlas.Rudvalis
open Atlas.Codes.Quaternary

theorem coordinateShellPiece_transitive (v w : coordinateShellPiece) :
    ∃g : codeGroup,g • v.val=w.val := by
  obtain ⟨a,ha⟩ := v.prop
  obtain ⟨b,hb⟩ := w.prop
  obtain ⟨g,hg⟩ := coordinateShell_transitive a b
  refine ⟨g,?_⟩
  rw [←ha,←hb]
  exact Subtype.ext (Subtype.ext hg)

theorem fourShellPiece_transitive (v w : fourShellPiece) :
    ∃g : codeGroup,g • v.val=w.val := by
  obtain ⟨a,ha⟩ := v.prop
  obtain ⟨b,hb⟩ := w.prop
  obtain ⟨g,hg⟩ := four_minimum_transitive a.val.val b.val.val a.val.prop b.val.prop
    a.prop.1 b.prop.1 a.prop.2 b.prop.2
  refine ⟨g,?_⟩
  rw [←ha,←hb,←minimumWordShellLift_equivariant]
  apply congrArg minimumWordShellLift
  exact Subtype.ext (Subtype.ext hg)

theorem heavyShellPiece_transitive (v w : heavyShellPiece) :
    ∃g : codeGroup,g • v.val=w.val := by
  obtain ⟨a,ha⟩ := v.prop
  obtain ⟨b,hb⟩ := w.prop
  obtain ⟨g,hg⟩ := heavy_minimum_transitive a.val.val b.val.val a.val.prop b.val.prop
    a.prop.1 b.prop.1 a.prop.2 b.prop.2
  refine ⟨g,?_⟩
  rw [←ha,←hb,←minimumWordShellLift_equivariant]
  apply congrArg minimumWordShellLift
  exact Subtype.ext (Subtype.ext hg)

theorem shellPieceCross_transitive (s : SubMulAction codeGroup MinimalShell)
    (ht : ∀v w : s,∃g : codeGroup,g • v.val=w.val)
    (v w : ShellPieceCross s) :
    ∃g : codeGroup,g • shellPieceCrossMap s v=shellPieceCrossMap s w := by
  induction v using Quotient.inductionOn
  induction w using Quotient.inductionOn
  rename_i v w
  obtain ⟨g,hg⟩ := ht v w
  refine ⟨g,?_⟩
  change g • minimalCross v.val=minimalCross w.val
  rw [←minimalCross_smul,hg]

theorem coordinateCrosses_transitive (v w : CoordinateCrosses) :
    ∃g : codeGroup,g • shellPieceCrossMap coordinateShellPiece v=shellPieceCrossMap coordinateShellPiece w :=
  shellPieceCross_transitive _ coordinateShellPiece_transitive v w

theorem fourBlockCrosses_transitive (v w : FourBlockCrosses) :
    ∃g : codeGroup,g • shellPieceCrossMap fourShellPiece v=shellPieceCrossMap fourShellPiece w :=
  shellPieceCross_transitive _ fourShellPiece_transitive v w

theorem heavyCrosses_transitive (v w : HeavyCrosses) :
    ∃g : codeGroup,g • shellPieceCrossMap heavyShellPiece v=shellPieceCrossMap heavyShellPiece w :=
  shellPieceCross_transitive _ heavyShellPiece_transitive v w

end Atlas.Rudvalis
