import Atlas.Fischer.MarkedPentadStabilizerBridges
import Atlas.Fischer.MarkedPentadSwitches

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes

/-- The actual fixing switches act transitively on the three frames. -/
theorem markedPentadFrame_transitive (S : Finset Omega) (hS : S.card=5) :
    MulAction.IsPretransitive (markedPentadPointwise S) (MarkedPentadFrame S) := by
  have hr (F : MarkedPentadFrame S) : ∃ g : markedPentadPointwise S,
      g • markedStandardFrame S=F := by
    obtain ⟨g,hg,hF⟩ := markedPentadFrame_reachable S hS F
    exact ⟨⟨g,(mem_markedPentadPointwise_iff S g).mpr hg⟩,Subtype.ext hF⟩
  constructor
  intro F K
  obtain ⟨g,hg⟩ := hr F
  obtain ⟨h,hh⟩ := hr K
  refine ⟨h*g⁻¹,?_⟩
  rw [mul_smul,← hg,inv_smul_smul,hh]

/-- Exact order of the actual pointwise commuting-pentad centralizer. -/
theorem markedPentadPointwise_order (a : Fin 5 ↪ Omega) :
    Nat.card (markedPentadPointwise (Finset.univ.image a))=589824 := by
  apply markedPentadPointwise_order_of_transitive
  apply markedPentadFrame_transitive
  rw [Finset.card_image_of_injective _ a.injective,Finset.card_univ,Fintype.card_fin]

theorem basicOrderedPentad_stabilizer_order (a : Fin 5 ↪ Omega) :
    Nat.card (MulAction.stabilizer rootGeneratedRayGroup (basicOrderedCommutingTuple a))=589824 := by
  rw [basicOrderedCommutingTuple_stabilizer,markedPentadPointwise_order]

end Atlas.Fischer
