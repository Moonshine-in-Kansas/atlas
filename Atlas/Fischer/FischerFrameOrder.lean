import Atlas.Fischer.FischerGroupOrder
import Atlas.Fischer.FischerFrameAction

noncomputable section
namespace Atlas.Fischer

/-- The standard frame as a point of the actual frame action. -/
def standardFischerFrame : FischerFrame := ⟨standardCommutingFrame,standardCommutingFrame_isFrame⟩

theorem standardFischerFrame_stabilizer :
    MulAction.stabilizer rootGeneratedRayGroup standardFischerFrame=standardFrameRayStabilizer := by
  ext g
  change (g • standardFischerFrame=standardFischerFrame) ↔
    g ∈ Subgroup.normalizer standardCommutingFrame
  rw [Subgroup.mem_normalizer_iff_conj_image_eq]
  exact ⟨fun h => congrArg Subtype.val h,fun h => Subtype.ext h⟩

theorem standardFrameRayStabilizer_order : Nat.card standardFrameRayStabilizer=1002795171840 := by
  rw [← Nat.card_congr parkerStandardFrameEquiv.toEquiv,parkerStandardGroup_order_value]

/-- Frame count from the actual transitive conjugation action and its proved
full Parker stabilizer, after the independent pentad group-order calculation. -/
theorem fischerFrame_count : Nat.card FischerFrame=2503413946215 := by
  haveI := fischerFrame_transitive
  have he : MulAction.orbit rootGeneratedRayGroup standardFischerFrame ≃ FischerFrame :=
    Equiv.setCongr (MulAction.orbit_eq_univ rootGeneratedRayGroup standardFischerFrame) |>.trans
      (Equiv.Set.univ _)
  have hc := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup rootGeneratedRayGroup standardFischerFrame)
  rw [Nat.card_prod,Nat.card_congr he,standardFischerFrame_stabilizer,
    standardFrameRayStabilizer_order,rootGeneratedRayGroup_order_value] at hc
  exact Nat.eq_of_mul_eq_mul_right (by decide : 0 < 1002795171840) hc

end Atlas.Fischer
