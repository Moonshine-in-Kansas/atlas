import Atlas.Rudvalis.LatticeShellPieces

namespace Atlas.Rudvalis

noncomputable abbrev ShellPieceCross (s : SubMulAction codeGroup MinimalShell) :=
  Quotient (MulAction.orbitRel GaussianUnits s)

theorem shellPieceCross_card (s : SubMulAction codeGroup MinimalShell) :
    Nat.card s=Nat.card (ShellPieceCross s)*4 := by
  have hf (g : GaussianUnits) (v : s) (h : g • v=v) : g=1 :=
    gaussianUnits_free g v.val (congrArg Subtype.val h)
  simpa only [gaussianUnits_card] using Atlas.free_action_card GaussianUnits s hf

noncomputable def shellPieceCrossMap (s : SubMulAction codeGroup MinimalShell) :
    ShellPieceCross s → MinimalCross :=
  Quotient.map (fun v : s => v.val) (by
    intro v w h
    obtain ⟨g,hg⟩ := MulAction.mem_orbit_iff.mp h
    exact MulAction.mem_orbit_iff.mpr ⟨g,congrArg Subtype.val hg⟩)

theorem shellPieceCrossMap_injective (s : SubMulAction codeGroup MinimalShell) :
    Function.Injective (shellPieceCrossMap s) := by
  intro v w
  induction v using Quotient.inductionOn
  induction w using Quotient.inductionOn
  intro h
  apply Quotient.sound
  obtain ⟨g,hg⟩ := MulAction.mem_orbit_iff.mp (Quotient.exact h)
  exact MulAction.mem_orbit_iff.mpr ⟨g,Subtype.ext hg⟩

noncomputable abbrev CoordinateCrosses := ShellPieceCross coordinateShellPiece
noncomputable abbrev FourBlockCrosses := ShellPieceCross fourShellPiece
noncomputable abbrev HeavyCrosses := ShellPieceCross heavyShellPiece

theorem coordinateCrosses_card : Nat.card CoordinateCrosses=28 := by
  change Nat.card (ShellPieceCross coordinateShellPiece)=28
  have h := shellPieceCross_card coordinateShellPiece
  rw [coordinateShellPiece_card] at h
  omega

theorem fourBlockCrosses_card : Nat.card FourBlockCrosses=448 := by
  change Nat.card (ShellPieceCross fourShellPiece)=448
  have h := shellPieceCross_card fourShellPiece
  rw [fourShellPiece_card] at h
  omega

theorem heavyCrosses_card : Nat.card HeavyCrosses=3584 := by
  change Nat.card (ShellPieceCross heavyShellPiece)=3584
  have h := shellPieceCross_card heavyShellPiece
  rw [heavyShellPiece_card] at h
  omega

end Atlas.Rudvalis
