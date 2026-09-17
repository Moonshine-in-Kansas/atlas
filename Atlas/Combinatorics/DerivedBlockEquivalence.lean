import Atlas.Combinatorics.DerivedSteiner

noncomputable section
namespace Atlas.Combinatorics
attribute [local instance] Classical.propDecidable

variable {α : Type*} [Fintype α] [DecidableEq α]

def derivedBlocksThroughEquiv (blocks : Finset (Finset α)) (a : α) :
    {B // B ∈ derivedBlocks blocks a} ≃ {O // O ∈ blocks ∧ a ∈ O} where
  toFun B := ⟨insert a (complementBlockLift a B.val),
    (derivedBlocks_mem blocks a B.val).mp B.prop,Finset.mem_insert_self _ _⟩
  invFun O := ⟨complementBlockRestrict a O.val,by
    rw [derivedBlocks_mem,complementBlock_restore a O.val O.prop.2]
    exact O.prop.1⟩
  left_inv B := by
    apply Subtype.ext
    ext x
    simp [complementBlockRestrict,complementBlockLift,x.prop]
  right_inv O := Subtype.ext (complementBlock_restore a O.val O.prop.2)

theorem derivedBlocksThroughEquiv_other_mem (blocks : Finset (Finset α)) (a : α)
    (b : PointComplement a) (B : {B // B ∈ derivedBlocks blocks a}) :
    b.val ∈ (derivedBlocksThroughEquiv blocks a B).val ↔ b ∈ B.val := by
  change b.val ∈ insert a (complementBlockLift a B.val) ↔ _
  simp [complementBlockLift,b.prop]

theorem derivedBlocks_through_card (blocks : Finset (Finset α)) (a : α) :
    (derivedBlocks blocks a).card = (blocks.filter (fun O => a ∈ O)).card := by
  have he := Nat.card_congr (derivedBlocksThroughEquiv blocks a)
  simpa only [Nat.card_eq_fintype_card,Fintype.card_coe,Fintype.card_subtype,
    Finset.filter_and,Finset.filter_mem_eq_inter,Finset.univ_inter,Finset.inter_filter,Finset.inter_univ] using he

end Atlas.Combinatorics
