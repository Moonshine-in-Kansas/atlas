import Atlas.Rudvalis.GaussianCrossAction
import Atlas.Rudvalis.LatticeCrossPieces

namespace Atlas.Rudvalis

noncomputable def coordinateFrame : Set MinimalCross := Set.range (shellPieceCrossMap coordinateShellPiece)

theorem coordinateFrame_card : Nat.card coordinateFrame=28 := by
  unfold coordinateFrame
  rw [Nat.card_congr (Equiv.ofInjective _ (shellPieceCrossMap_injective coordinateShellPiece)).symm]
  exact coordinateCrosses_card

theorem minimalCross_mem_coordinateFrame (v : MinimalShell) :
    minimalCross v∈coordinateFrame ↔ v∈coordinateShellPiece := by
  constructor
  · rintro ⟨c,hc⟩
    induction c using Quotient.inductionOn with
    | h w =>
      change minimalCross w.val=minimalCross v at hc
      obtain ⟨u,hu⟩ := (minimalCross_eq_iff _ _).mp hc
      have hm := SMulMemClass.smul_mem (u.val⁻¹) w.prop
      change u.val • v=w.val at hu
      rw [←hu,inv_smul_smul] at hm
      exact hm
  · intro h
    exact ⟨Quotient.mk _ ⟨v,h⟩,rfl⟩

theorem coordinateShellPiece_iff (v : MinimalShell) :
    v∈coordinateShellPiece ↔ coordinateShell v.val.val := by
  constructor
  · rintro ⟨⟨i,b⟩,rfl⟩
    cases b <;> exact ⟨i,by simp [coordinateShellLift]⟩
  · rintro ⟨i,hi|hi⟩
    · exact ⟨(i,true),Subtype.ext (Subtype.ext hi.symm)⟩
    · exact ⟨(i,false),Subtype.ext (Subtype.ext hi.symm)⟩

theorem coordinateFrame_code_stable (g : codeGroup) (c : MinimalCross)
    (hc : c∈coordinateFrame) : g • c∈coordinateFrame := by
  induction c using Quotient.inductionOn with
  | h v =>
    change minimalCross (g • v)∈coordinateFrame
    exact (minimalCross_mem_coordinateFrame _).mpr
      (SMulMemClass.smul_mem g ((minimalCross_mem_coordinateFrame v).mp hc))

/-- Exact stabilizer of the 28 actual coordinate Gaussian crosses. -/
theorem gaussian_frame_stabilizer (f : gaussianLatticeGroup) :
    (∀c,c∈coordinateFrame ↔ f • c∈coordinateFrame) ↔
    ∃g : codeGroup,codeGaussianHom g=f := by
  constructor
  · intro h
    apply (gaussian_coordinate_stabilizer f).mp
    intro i
    let v : MinimalShell := ⟨⟨coordinateMinimum i,coordinateMinimum_mem i⟩,coordinateMinimum_norm i⟩
    have hv : v∈coordinateShellPiece := ⟨(i,true),rfl⟩
    have hc := (h (minimalCross v)).mp ((minimalCross_mem_coordinateFrame v).mpr hv)
    exact (coordinateShellPiece_iff (f • v)).mp ((minimalCross_mem_coordinateFrame _).mp hc)
  · rintro ⟨g,rfl⟩ c
    rw [codeGaussianHom_cross]
    constructor
    · exact coordinateFrame_code_stable g c
    · intro h
      have hi := coordinateFrame_code_stable g⁻¹ (g • c) h
      simpa using hi

end Atlas.Rudvalis
