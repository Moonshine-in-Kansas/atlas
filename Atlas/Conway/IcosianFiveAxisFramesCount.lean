import Atlas.Conway.IcosianFiveAxisFrames

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Conway
open Atlas.Combinatorics
attribute [local instance] Classical.propDecidable

private theorem axisNeighbor_ne_axis (p : IcosianAxisNeighbor) : p.val≠icosianRootAxisPoint 0 := by
  intro h
  have hp := p.property
  rw [h] at hp
  exact icosianRootPointOrthogonal_irrefl _ hp

private theorem eightNeighbor_val_injective : Function.Injective (fun i => (icosianEightNeighborPoint i).val) :=
  fun _ _ h => icosianEightNeighborPoint_injective (Subtype.ext h)

theorem icosianLocalEdgeRootFrame_injective : Function.Injective icosianLocalEdgeRootFrame := by
  intro i j h
  have hi : (icosianEightNeighborPoint (icosianFirstFourIndex i)).val∈(icosianLocalEdgeRootFrame j).val := by
    rw [← h]
    simp [icosianLocalEdgeRootFrame,relationTriangleOfTriple]
  change (icosianEightNeighborPoint (icosianFirstFourIndex i)).val∈
    ({icosianRootAxisPoint 0,(icosianEightNeighborPoint (icosianFirstFourIndex j)).val,
      (icosianEightNeighborPoint (icosianEightPartnerIndex (icosianFirstFourIndex j))).val} : Finset IcosianRootPoint) at hi
  simp only [Finset.mem_insert,Finset.mem_singleton] at hi
  rcases hi with hi | hi | hi
  · exact (axisNeighbor_ne_axis _ hi).elim
  · apply Fin.ext
    exact congrArg (fun k : Fin 8 => k.val) (eightNeighbor_val_injective hi)
  · have he := congrArg (fun k : Fin 8 => k.val) (eightNeighbor_val_injective hi)
    change i.val=7-j.val at he
    omega

theorem icosianLocalCoordinateRootFrame_ne_edge (j : Fin 4) :
    icosianLocalCoordinateRootFrame≠icosianLocalEdgeRootFrame j := by
  intro h
  have hi : (icosianEightNeighborPoint (icosianFirstFourIndex j)).val∈icosianLocalCoordinateRootFrame.val := by
    rw [h]
    simp [icosianLocalEdgeRootFrame,relationTriangleOfTriple]
  change (icosianEightNeighborPoint (icosianFirstFourIndex j)).val∈
    ({icosianRootAxisPoint 0,icosianRootAxisPoint 1,icosianRootAxisPoint 2} : Finset IcosianRootPoint) at hi
  simp only [Finset.mem_insert,Finset.mem_singleton] at hi
  rcases hi with hi | hi | hi
  · exact axisNeighbor_ne_axis _ hi
  · exact icosianEightNeighbor_ne_twoAxis _ 0 (Subtype.ext hi)
  · exact icosianEightNeighbor_ne_twoAxis _ 1 (Subtype.ext hi)

theorem icosianFiveAxisFrames_injective : Function.Injective icosianFiveAxisFrames := by
  intro i j h
  cases i with
  | inl u =>
    cases j with
    | inl v => exact congrArg Sum.inl (Subsingleton.elim u v)
    | inr k => exact (icosianLocalCoordinateRootFrame_ne_edge k h).elim
  | inr k =>
    cases j with
    | inl u => exact (icosianLocalCoordinateRootFrame_ne_edge k h.symm).elim
    | inr l => exact congrArg Sum.inr (icosianLocalEdgeRootFrame_injective h)

abbrev IcosianAxisRootFrames :=
  {F : IcosianRootFrame // icosianRootAxisPoint 0∈F.val}

def icosianAxisRootFramesEquiv : (Unit ⊕ Fin 4) ≃ IcosianAxisRootFrames :=
  Equiv.ofBijective (fun i => ⟨icosianFiveAxisFrames i,icosianFiveAxisFrames_contains_axis i⟩)
    ⟨fun _ _ h => icosianFiveAxisFrames_injective (congrArg Subtype.val h),by
      rintro ⟨F,hF⟩
      obtain ⟨i,hi⟩ := icosianFiveAxisFrames_exhaust F hF
      exact ⟨i,Subtype.ext hi⟩⟩

theorem icosianAxisRootFrames_card : Nat.card IcosianAxisRootFrames=5 := by
  rw [← Nat.card_congr icosianAxisRootFramesEquiv,Nat.card_sum]
  norm_num

end Atlas.Conway
