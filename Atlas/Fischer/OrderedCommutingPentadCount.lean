import Atlas.Fischer.OrderedCommutingTuples

noncomputable section
namespace Atlas.Fischer
open scoped BigOperators

instance orderedCommutingTuple_fintype (s : ℕ) : Fintype (OrderedCommutingTuple s) :=
  Fintype.ofFinite _

theorem orderedCommutingTuple_zero_card : Nat.card (OrderedCommutingTuple 0)=1 := by
  apply Nat.card_eq_one_iff_unique.mpr
  refine ⟨?_,?_⟩
  · constructor
    intro x y
    apply Subtype.ext
    apply Function.Embedding.ext
    intro k
    exact Fin.elim0 k
  · exact ⟨⟨Function.Embedding.ofIsEmpty,fun k => Fin.elim0 k,fun k => Fin.elim0 k⟩⟩

/-- Successive extension counting for the actual ordered tuples. -/
theorem orderedCommutingTuple_succ_card (s : ℕ) (hs : s ≤ 5) :
    Nat.card (OrderedCommutingTuple (s+1)) = Nat.card (OrderedCommutingTuple s) *
      ![306936,31671,3510,693,180,51] ⟨s,by omega⟩ := by
  rw [Nat.card_congr (orderedCommutingSuccEquiv s), Nat.card_sigma]
  have he (t : OrderedCommutingTuple s) := commutingExtension_card hs t.val t.property.1 t.property.2
  simp only [he,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Nat.card_eq_fintype_card]
  norm_cast

/-- Ordered commuting pentads counted structurally through five extension stages. -/
theorem orderedCommutingPentad_card : Nat.card (OrderedCommutingTuple 5) =
    306936 * 31671 * 3510 * 693 * 180 := by
  rw [orderedCommutingTuple_succ_card 4 (by omega),
    orderedCommutingTuple_succ_card 3 (by omega),
    orderedCommutingTuple_succ_card 2 (by omega),
    orderedCommutingTuple_succ_card 1 (by omega),
    orderedCommutingTuple_succ_card 0 (by omega),orderedCommutingTuple_zero_card]
  norm_num

end Atlas.Fischer
