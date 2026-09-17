import Atlas.Combinatorics.DerivedBlockEquivalence
import Atlas.Mathieu.Mathieu22Witt

noncomputable section
namespace Atlas.Codes
open Atlas.Combinatorics
attribute [local instance] Classical.propDecidable
local instance (a : Omega) : Fintype (Mathieu23Points a) := Fintype.ofFinite _
local instance (a : Omega) (b : Mathieu23Points a) : Fintype (Mathieu22Points a b) := Fintype.ofFinite _

theorem octads_through_point_card (a : Omega) :
    (octads.filter (fun O => a ∈ O)).card = 253 := by
  rw [← derivedBlocks_through_card]
  exact mathieu23Blocks_card a

def octadsThroughPairEquiv (a : Omega) (b : Mathieu23Points a) :
    {B // B ∈ mathieu23Blocks a ∧ b ∈ B} ≃ {O // O ∈ octads ∧ a ∈ O ∧ b.val ∈ O} := by
  let e : {B // B ∈ mathieu23Blocks a} ≃ {O // O ∈ octads ∧ a ∈ O} :=
    derivedBlocksThroughEquiv octads a
  refine {
    toFun := fun B => ⟨(e ⟨B.val,B.prop.1⟩).val,(e ⟨B.val,B.prop.1⟩).prop.1,
      (e ⟨B.val,B.prop.1⟩).prop.2,?_⟩
    invFun := fun O => ⟨(e.symm ⟨O.val,O.prop.1,O.prop.2.1⟩).val,
      (e.symm ⟨O.val,O.prop.1,O.prop.2.1⟩).prop,?_⟩
    left_inv := ?_
    right_inv := ?_ }
  · exact (derivedBlocksThroughEquiv_other_mem octads a b ⟨B.val,B.prop.1⟩).mpr B.prop.2
  · have h := O.prop.2.2
    have he := congrArg Subtype.val (e.apply_symm_apply ⟨O.val,O.prop.1,O.prop.2.1⟩)
    rw [← he] at h
    exact (derivedBlocksThroughEquiv_other_mem octads a b _).mp h
  · intro B
    apply Subtype.ext
    exact congrArg (fun z : {B // B ∈ mathieu23Blocks a} => z.val) (e.symm_apply_apply ⟨B.val,B.prop.1⟩)
  · intro O
    apply Subtype.ext
    exact congrArg (fun z : {O // O ∈ octads ∧ a ∈ O} => z.val) (e.apply_symm_apply ⟨O.val,O.prop.1,O.prop.2.1⟩)

theorem octads_through_pair_card (a b : Omega) (hab : a ≠ b) :
    (octads.filter (fun O => a ∈ O ∧ b ∈ O)).card = 77 := by
  let b' : Mathieu23Points a := ⟨b,hab.symm⟩
  have e := (derivedBlocksThroughEquiv (mathieu23Blocks a) b').trans (octadsThroughPairEquiv a b')
  have hc := Nat.card_congr e
  have he : {O // O ∈ octads ∧ a ∈ O ∧ b ∈ O} ≃
      {O // O ∈ octads.filter (fun O => a ∈ O ∧ b ∈ O)} :=
    Equiv.subtypeEquivRight (fun O => by simp)
  rw [Nat.card_congr he] at hc
  simp only [Nat.card_eq_fintype_card,Fintype.card_coe] at hc
  change (mathieu22Blocks a b').card = _ at hc
  rw [mathieu22Blocks_card] at hc
  exact hc.symm

theorem octads_avoiding_pair_card (a b : Omega) (hab : a ≠ b) :
    (octads.filter (fun O => a ∉ O ∧ b ∉ O)).card = 330 := by
  have hU : octads.filter (fun O => a ∈ O ∨ b ∈ O) =
      octads.filter (fun O => a ∈ O) ∪ octads.filter (fun O => b ∈ O) := by ext O; simp; tauto
  have hI : octads.filter (fun O => a ∈ O) ∩ octads.filter (fun O => b ∈ O) =
      octads.filter (fun O => a ∈ O ∧ b ∈ O) := by ext O; simp; tauto
  have hcount := Finset.card_union_add_card_inter (octads.filter (fun O => a ∈ O))
    (octads.filter (fun O => b ∈ O))
  rw [hI,octads_through_pair_card a b hab,octads_through_point_card,octads_through_point_card] at hcount
  have hcompl := Finset.card_filter_add_card_filter_not (s := octads) (p := fun O => a ∈ O ∨ b ∈ O)
  rw [hU,octads_card] at hcompl
  have he : octads.filter (fun O => ¬ (a ∈ O ∨ b ∈ O)) =
      octads.filter (fun O => a ∉ O ∧ b ∉ O) := by ext O; simp
  rw [he] at hcompl
  omega

end Atlas.Codes
