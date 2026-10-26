import Atlas.Rudvalis.LocalFusionGroup
import Atlas.GroupTheory.OrbitPreimageCard

namespace Atlas.Rudvalis

theorem localFusion_orbit_orthogonal (c : MinimalCross)
    (hc : c∈MulAction.orbit localFusionGroup localThirdCross) : CrossOrthogonal localReferenceCross c := by
  obtain ⟨g,rfl⟩ := MulAction.mem_orbit_iff.mp hc
  have h := (crossOrthogonal_gaussian g.val _ _).mpr localFusion_first_third_orthogonal
  change CrossOrthogonal (g • localReferenceCross) (g • localThirdCross) at h
  rw [localFusionGroup_fix] at h
  exact h

theorem localFusion_coordinate_orbit_preimage_card :
    Nat.card {c : CoordinateCrosses // shellPieceCrossMap coordinateShellPiece c∈
      MulAction.orbit localFusionGroup localThirdCross}=27 := by
  have he (c : CoordinateCrosses) :
      shellPieceCrossMap coordinateShellPiece c∈MulAction.orbit localFusionGroup localThirdCross ↔
      CrossOrthogonal localReferenceCross (shellPieceCrossMap coordinateShellPiece c) := by
    constructor
    · exact localFusion_orbit_orthogonal _
    · intro h
      apply localFusionGroup_coordinate_complement
      refine ⟨⟨c,rfl⟩,?_⟩
      intro hbad
      rw [hbad] at h
      exact crossOrthogonal_irrefl _ h
  rw [Nat.card_congr (Equiv.subtypeEquivRight he)]
  exact coordinateOrthogonalCrosses_card _ _

theorem codeReference_transport_to_local {v w : MinimalCross}
    (h : ∃g : codeReferenceStabilizer,g.val • v=w) :
    ∃g : localFusionGroup,g • v=w := by
  obtain ⟨g,hg⟩ := h
  refine ⟨⟨codeReferenceGaussianHom g,codeReferenceGaussianHom_mem g⟩,?_⟩
  change codeGaussianHom g.val • v=w
  rw [codeGaussianHom_cross]
  exact hg

/-- The numerical alternatives follow from actual transitivity on the two
noncoordinate pieces. Both outstanding geometric inputs remain explicit. -/
theorem localFusion_orbit_sizes_of_piece_transitivity
    (hfour : ∀v w : FourBlockCrosses,
      CrossOrthogonal localReferenceCross (shellPieceCrossMap fourShellPiece v) →
      CrossOrthogonal localReferenceCross (shellPieceCrossMap fourShellPiece w) →
      ∃g : codeReferenceStabilizer,g.val • shellPieceCrossMap fourShellPiece v=shellPieceCrossMap fourShellPiece w)
    (hheavy : ∀v w : HeavyCrosses,
      CrossOrthogonal localReferenceCross (shellPieceCrossMap heavyShellPiece v) →
      CrossOrthogonal localReferenceCross (shellPieceCrossMap heavyShellPiece w) →
      ∃g : codeReferenceStabilizer,g.val • shellPieceCrossMap heavyShellPiece v=shellPieceCrossMap heavyShellPiece w) :
    Nat.card (MulAction.orbit localFusionGroup localThirdCross)=27 ∨
    Nat.card (MulAction.orbit localFusionGroup localThirdCross)=219 ∨
    Nat.card (MulAction.orbit localFusionGroup localThirdCross)=1563 ∨
    Nat.card (MulAction.orbit localFusionGroup localThirdCross)=1755 := by
  have hf := Atlas.GroupTheory.orbit_preimage_card_zero_or
    (G := localFusionGroup) (shellPieceCrossMap fourShellPiece)
    (fun c => CrossOrthogonal localReferenceCross (shellPieceCrossMap fourShellPiece c)) localThirdCross
    (fun _ => localFusion_orbit_orthogonal _) (fun v w hv hw => codeReference_transport_to_local (hfour v w hv hw))
  have hh := Atlas.GroupTheory.orbit_preimage_card_zero_or
    (G := localFusionGroup) (shellPieceCrossMap heavyShellPiece)
    (fun c => CrossOrthogonal localReferenceCross (shellPieceCrossMap heavyShellPiece c)) localThirdCross
    (fun _ => localFusion_orbit_orthogonal _) (fun v w hv hw => codeReference_transport_to_local (hheavy v w hv hw))
  rw [show Nat.card {c : FourBlockCrosses // CrossOrthogonal localReferenceCross (shellPieceCrossMap fourShellPiece c)}=192 from fourOrthogonalCrosses_card _ _] at hf
  rw [show Nat.card {c : HeavyCrosses // CrossOrthogonal localReferenceCross (shellPieceCrossMap heavyShellPiece c)}=1536 from heavyOrthogonalCrosses_card _ _] at hh
  have hc := crossPiece_condition_card (fun c => c∈MulAction.orbit localFusionGroup localThirdCross)
  rw [localFusion_coordinate_orbit_preimage_card] at hc
  change Nat.card (MulAction.orbit localFusionGroup localThirdCross)=_ at hc
  rcases hf with hf|hf <;> rcases hh with hh|hh <;> rw [hf,hh] at hc <;> omega

end Atlas.Rudvalis
