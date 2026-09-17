import Atlas.Fischer.MarkedPentadCentralizerOrder
import Atlas.Fischer.OrderedCommutingPentadCount

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes

/-- Independent order calculation: exact pentad orbit size multiplied by its
actual three-frame centralizer order, with no simplicity input. -/
theorem rootGeneratedRayGroup_order_product : Nat.card rootGeneratedRayGroup=
    589824*(306936*31671*3510*693*180) := by
  obtain ⟨a : Fin 5 ↪ Omega⟩ := Function.Embedding.nonempty_of_card_le
    (show Fintype.card (Fin 5) ≤ Fintype.card Omega by decide)
  have hc := orderedCommutingTuple_order_product 5 (by omega) (basicOrderedCommutingTuple a)
  rw [orderedCommutingPentad_card,basicOrderedCommutingTuple_stabilizer,
    markedPentadPointwise_order a] at hc
  exact hc.symm.trans (Nat.mul_comm _ _)

theorem rootGeneratedRayGroup_order_factored : Nat.card rootGeneratedRayGroup=
    2^22*3^16*5^2*7^3*11*13*17*23*29 := by
  rw [rootGeneratedRayGroup_order_product]
  norm_num

theorem rootGeneratedRayGroup_order_value :
    Nat.card rootGeneratedRayGroup=2510411418381323442585600 := by
  rw [rootGeneratedRayGroup_order_product]

/-- Every actual ordered commuting pentad has the same verified centralizer
order, through the existing transitive tuple action. -/
theorem orderedCommutingPentad_stabilizer_order (t : OrderedCommutingTuple 5) :
    Nat.card (MulAction.stabilizer rootGeneratedRayGroup t)=589824 := by
  have hc := orderedCommutingTuple_order_product 5 (by omega) t
  rw [orderedCommutingPentad_card,rootGeneratedRayGroup_order_value] at hc
  norm_num at hc
  change 4256204254796894400 * Nat.card (MulAction.stabilizer rootGeneratedRayGroup t)=2510411418381323442585600 at hc
  omega

end Atlas.Fischer
