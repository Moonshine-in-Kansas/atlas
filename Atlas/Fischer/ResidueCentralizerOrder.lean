import Atlas.Fischer.FischerGroupOrder

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes

/-- Enumerate the actual marked set, without changing its coordinates. -/
def residueCoordinateEmbedding (S : Finset Omega) : Fin S.card ↪ Omega :=
  (S.equivFin).symm.toEmbedding.trans (Function.Embedding.subtype _)

theorem residueCoordinateEmbedding_image (S : Finset Omega) :
    Finset.univ.image (residueCoordinateEmbedding S) = S := by
  classical
  ext i
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨k, rfl⟩
    exact ((S.equivFin).symm k).property
  · intro hi
    refine ⟨S.equivFin ⟨i,hi⟩, ?_⟩
    change ((S.equivFin).symm ((S.equivFin) ⟨i,hi⟩)).val = i
    rw [Equiv.symm_apply_apply]

/-- The literal centralizer is the stabilizer of the actual ordered marking. -/
theorem markedCentralizer_order_product (S : Finset Omega) (hS : S.card ≤ 5) :
    Nat.card (OrderedCommutingTuple S.card) * Nat.card (markedPentadPointwise S) =
      Nat.card rootGeneratedRayGroup := by
  have h := orderedCommutingTuple_order_product S.card hS
    (basicOrderedCommutingTuple (residueCoordinateEmbedding S))
  rw [basicOrderedCommutingTuple_stabilizer, residueCoordinateEmbedding_image] at h
  exact h

theorem orderedCommutingSingleton_card : Nat.card (OrderedCommutingTuple 1) = 306936 := by
  rw [orderedCommutingTuple_succ_card 0 (by omega), orderedCommutingTuple_zero_card]
  norm_num

theorem orderedCommutingPair_card : Nat.card (OrderedCommutingTuple 2) = 306936 * 31671 := by
  rw [orderedCommutingTuple_succ_card 1 (by omega), orderedCommutingSingleton_card]
  norm_num

/-- Exact order of the full one-point centralizer, before any residue quotient. -/
theorem markedCentralizer_singleton_order (S : Finset Omega) (hS : S.card = 1) :
    Nat.card (markedPentadPointwise S) = 8178940946586009600 := by
  have h := markedCentralizer_order_product S (by omega)
  rw [hS, orderedCommutingSingleton_card, rootGeneratedRayGroup_order_value] at h
  omega

/-- Exact order of the full commuting-pair centralizer, before any residue quotient. -/
theorem markedCentralizer_pair_order (S : Finset Omega) (hS : S.card = 2) :
    Nat.card (markedPentadPointwise S) = 258247006617600 := by
  have h := markedCentralizer_order_product S (by omega)
  rw [hS, orderedCommutingPair_card, rootGeneratedRayGroup_order_value] at h
  norm_num at h
  omega

end Atlas.Fischer
