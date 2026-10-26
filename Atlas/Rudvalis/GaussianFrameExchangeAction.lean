import Atlas.Rudvalis.GaussianFrameExchange
import Atlas.Rudvalis.SecondFrameCrosses
import Mathlib.Data.Set.Card

namespace Atlas.Rudvalis

 theorem originalFrame_signed_axis (i : SeedCoordinate) :
    originalFrame i=
      if i.2=0 then -coordinateMinimum (seedCoordinateEquiv (i.1,signedPositionIndex i.2))
      else coordinateMinimum (seedCoordinateEquiv (i.1,signedPositionIndex i.2)) := by
  funext z
  obtain ⟨j,rfl⟩ := seedCoordinateEquiv.surjective z
  rcases i with ⟨r,k⟩
  rcases j with ⟨s,l⟩
  simp only [originalFrame,seedTransportLinear_apply]
  decide +kernel +revert

theorem originalFrame_coordinateShell (i : SeedCoordinate) :
    coordinateShell (originalFrame i) := by
  refine ⟨seedCoordinateEquiv (i.1,signedPositionIndex i.2),?_⟩
  rw [originalFrame_signed_axis]
  split_ifs
  · exact Or.inr rfl
  · exact Or.inl rfl

theorem secondFrameCrosses_subset_exchange_image :
    secondFrameCrosses ⊆ (fun c:MinimalCross=>gaussianFrameExchange • c) '' coordinateFrame := by
  rintro _ ⟨i,rfl⟩
  let v : MinimalShell := gaussianFrameExchange⁻¹ • secondFrameShell (secondFrameOddIndex i)
  have happ (g : gaussianLatticeGroup) (w : MinimalShell) :
      (g • w).val.val=g.val w.val.val := rfl
  have hv : v.val.val=originalFrame (secondFrameOddIndex i) := by
    dsimp only [v]
    rw [happ,Subgroup.coe_inv,gaussianFrameExchange_val]
    apply frameComparison.injective
    change frameComparison (frameComparison.symm (secondFrame (secondFrameOddIndex i)))=_
    rw [LinearEquiv.apply_symm_apply]
    exact (frameComparison_originalFrame _).symm
  refine ⟨minimalCross v,?_,?_⟩
  · apply (minimalCross_mem_coordinateFrame v).mpr
    apply (coordinateShellPiece_iff v).mpr
    rw [hv]
    exact originalFrame_coordinateShell _
  · change minimalCross (gaussianFrameExchange • v)=minimalCross (secondFrameShell _)
    simp [v]

/-- The actual lattice isometry exchanges the two verified sets of 28 Gaussian crosses. -/
theorem gaussianFrameExchange_coordinateFrame :
    (fun c:MinimalCross=>gaussianFrameExchange • c) '' coordinateFrame=secondFrameCrosses := by
  symm
  apply Set.eq_of_subset_of_ncard_le secondFrameCrosses_subset_exchange_image
  rw [Set.ncard_image_of_injective _ (MulAction.injective gaussianFrameExchange),
    ←Nat.card_coe_set_eq,←Nat.card_coe_set_eq,coordinateFrame_card,secondFrameCrosses_card]

end Atlas.Rudvalis
