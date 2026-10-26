import Atlas.Rudvalis.LatticeCrossOrbits

namespace Atlas.Rudvalis
open Atlas.Codes.Quaternary

theorem coordinate_four_shell_disjoint (v : MinimalShell) :
    v∈coordinateShellPiece → v∈fourShellPiece → False := by
  rintro ⟨a,ha⟩ ⟨b,hb⟩
  exact coordinateShellLift_ne_minimumWordShellLift a (fourMinimumWord b) (ha.trans hb.symm)

theorem coordinate_heavy_shell_disjoint (v : MinimalShell) :
    v∈coordinateShellPiece → v∈heavyShellPiece → False := by
  rintro ⟨a,ha⟩ ⟨b,hb⟩
  exact coordinateShellLift_ne_minimumWordShellLift a (heavyMinimumWord b) (ha.trans hb.symm)

theorem four_heavy_shell_disjoint (v : MinimalShell) :
    v∈fourShellPiece → v∈heavyShellPiece → False := by
  rintro ⟨a,ha⟩ ⟨b,hb⟩
  have he := minimumWordShellLift_injective (ha.trans hb.symm)
  have hw := congrArg (fun w : MinimumWords => w.val.val) he
  exact four_heavy_disjoint _ a.prop.2 (hw ▸ b.prop.2)

theorem shellPieceCrossMap_disjoint (s t : SubMulAction codeGroup MinimalShell)
    (hd : ∀v : MinimalShell,v∈s → v∈t → False)
    (v : ShellPieceCross s) (w : ShellPieceCross t) :
    shellPieceCrossMap s v≠shellPieceCrossMap t w := by
  induction v using Quotient.inductionOn
  induction w using Quotient.inductionOn
  rename_i v w
  intro h
  obtain ⟨g,hg⟩ := MulAction.mem_orbit_iff.mp (Quotient.exact h)
  change g.val • w.val=v.val at hg
  apply hd v.val v.prop
  rw [←hg]
  exact t.smul_mem' g.val w.prop

theorem coordinate_four_cross_disjoint (v : CoordinateCrosses) (w : FourBlockCrosses) :
    shellPieceCrossMap coordinateShellPiece v≠shellPieceCrossMap fourShellPiece w :=
  shellPieceCrossMap_disjoint _ _ coordinate_four_shell_disjoint v w

theorem coordinate_heavy_cross_disjoint (v : CoordinateCrosses) (w : HeavyCrosses) :
    shellPieceCrossMap coordinateShellPiece v≠shellPieceCrossMap heavyShellPiece w :=
  shellPieceCrossMap_disjoint _ _ coordinate_heavy_shell_disjoint v w

theorem four_heavy_cross_disjoint (v : FourBlockCrosses) (w : HeavyCrosses) :
    shellPieceCrossMap fourShellPiece v≠shellPieceCrossMap heavyShellPiece w :=
  shellPieceCrossMap_disjoint _ _ four_heavy_shell_disjoint v w

theorem minimalShell_piece_cases (v : MinimalShell) :
    v∈coordinateShellPiece ∨ v∈fourShellPiece ∨ v∈heavyShellPiece := by
  rcases rudvalisLattice_shell_cases v.val.val v.val.prop v.prop with h|⟨w,hw⟩
  · left
    obtain ⟨i,hi|hi⟩ := h
    · exact ⟨(i,true),Subtype.ext (Subtype.ext hi.symm)⟩
    · exact ⟨(i,false),Subtype.ext (Subtype.ext hi.symm)⟩
  · right
    rcases quaternary_minimum_support_cases w.val.val w.val.prop w.prop with hf|hh
    · left
      exact ⟨⟨w.val,w.prop,hf⟩,Subtype.ext (Subtype.ext hw.symm)⟩
    · right
      exact ⟨⟨w.val,w.prop,hh⟩,Subtype.ext (Subtype.ext hw.symm)⟩

theorem minimalCross_piece_cases (v : MinimalCross) :
    (∃a : CoordinateCrosses,shellPieceCrossMap coordinateShellPiece a=v) ∨
    (∃a : FourBlockCrosses,shellPieceCrossMap fourShellPiece a=v) ∨
    (∃a : HeavyCrosses,shellPieceCrossMap heavyShellPiece a=v) := by
  induction v using Quotient.inductionOn
  rename_i v
  rcases minimalShell_piece_cases v with hc|hf|hh
  · exact Or.inl ⟨Quotient.mk _ ⟨v,hc⟩,rfl⟩
  · exact Or.inr (Or.inl ⟨Quotient.mk _ ⟨v,hf⟩,rfl⟩)
  · exact Or.inr (Or.inr ⟨Quotient.mk _ ⟨v,hh⟩,rfl⟩)

theorem shellPieceCrossMap_image_stable (s : SubMulAction codeGroup MinimalShell)
    (g : codeGroup) (v : ShellPieceCross s) :
    ∃w : ShellPieceCross s,shellPieceCrossMap s w=g • shellPieceCrossMap s v := by
  induction v using Quotient.inductionOn
  rename_i v
  refine ⟨Quotient.mk _ (g • v),?_⟩
  rfl

end Atlas.Rudvalis

