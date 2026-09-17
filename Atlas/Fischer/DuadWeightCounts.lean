import Atlas.Fischer.DuadWeightCoordinates

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Fischer
open Atlas.Codes
attribute [local instance] Classical.propDecidable

theorem octad_predicate_card (P : Finset Omega → Prop) :
    Nat.card {O : Octad // P O.val}=(octads.filter P).card := by
  let e : {O : Octad // P O.val} ≃ {O // O ∈ octads.filter P} :=
    { toFun := fun O => ⟨O.val.val,Finset.mem_filter.mpr ⟨O.val.property,O.property⟩⟩
      invFun := fun O => ⟨⟨O.val,(Finset.mem_filter.mp O.property).1⟩,(Finset.mem_filter.mp O.property).2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Nat.card_congr e,Nat.card_eq_fintype_card,Fintype.card_coe]

theorem duadShortened_weight_eight_card (p : Finset Omega) (hp : p.card=2) :
    Nat.card {c : duadShortenedCode p // hammingNorm c.val.val=8}=330 := by
  rw [Nat.card_congr (duadWeightEightEquiv p),octad_predicate_card]
  have he : octads.filter (fun O => Disjoint p O)=
      octads.filter (fun O => ∅ ⊆ O ∧ (O ∩ p).card=0) := by
    ext O
    simp [Finset.disjoint_iff_inter_eq_empty,Finset.inter_comm]
  convert (congrArg Finset.card he).trans (octad_duad_distribution p hp).2.2 using 1
  congr 1
  ext O
  simp

theorem duadShortened_weight_sixteen_card (p : Finset Omega) (hp : p.card=2) :
    Nat.card {c : duadShortenedCode p // hammingNorm c.val.val=16}=77 := by
  rw [Nat.card_congr (duadWeightSixteenEquiv p),octad_predicate_card]
  convert octadReplication_two p hp using 1
  unfold octadReplication
  congr 1
  ext O
  simp

end Atlas.Fischer
