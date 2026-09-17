import Atlas.Conway.Co3HeptadDot

noncomputable section
namespace Atlas.Conway
open Atlas.Codes Atlas.Lattices
attribute [local instance] Classical.propDecidable
local instance co3NeighbourPointsFintype (a : Omega) : Fintype (Mathieu23Points a) := Fintype.ofFinite _

theorem co3_heptad_filter_card (a : Omega) (P : Finset (Mathieu23Points a) → Prop) :
    (Finset.univ.filter (fun B : Co3Heptads a => P B.val)).card =
      ((mathieu23Blocks a).filter P).card := by
  let e : {B : Co3Heptads a // P B.val} ≃ {B // B ∈ (mathieu23Blocks a).filter P} :=
    (Equiv.subtypeSubtypeEquivSubtypeInter (fun B => B ∈ mathieu23Blocks a) P).trans
      (Equiv.subtypeEquivRight (fun _ => by simp))
  have h := Nat.card_congr e
  simpa only [Nat.card_eq_fintype_card,Fintype.card_subtype,
    Finset.filter_mem_eq_inter,Finset.univ_inter] using h

def co3ThroughHeptadVectors (a : Omega) (b : Mathieu23Points a) : Finset leech :=
  (Finset.univ.filter (fun B : Co3Heptads a => b ∈ B.val)).image (co3HeptadEndpoint a)

theorem co3ThroughHeptadVectors_mem (a : Omega) (b : Mathieu23Points a) (y : leech) :
    y ∈ co3ThroughHeptadVectors a b ↔ ∃ B : Co3Heptads a, b ∈ B.val ∧ co3HeptadEndpoint a B = y := by
  simp [co3ThroughHeptadVectors]

theorem co3_point_heptad_neighbours (a : Omega) (b c : Mathieu23Points a) (hbc : b ≠ c) :
    ((co3ThroughHeptadVectors a b).filter
      (fun y => integerDot (minimumPairPlus a c.val).val y.val = 16)).card = 21 := by
  rw [co3ThroughHeptadVectors,Finset.filter_image,
    Finset.card_image_of_injective _ (co3HeptadEndpoint_injective a),Finset.filter_filter]
  have he (B : Co3Heptads a) : integerDot (minimumPairPlus a c.val).val (co3HeptadEndpoint a B).val = 16 ↔ c ∈ B.val := by
    rw [co3Point_heptad_dot]; split_ifs <;> simp_all
  simp_rw [he]
  calc
    _ = ((mathieu23Blocks a).filter (fun B => b ∈ B ∧ c ∈ B)).card := by
      convert co3_heptad_filter_card a (fun B => b ∈ B ∧ c ∈ B) using 1 <;> congr 1 <;> ext B <;> simp [mathieu23Blocks]
    _ = 21 := by
      convert mathieu23Blocks_through_pair_card a b c hbc using 1 <;> congr 1 <;> ext B <;> simp [mathieu23Blocks]

theorem co3_complement_heptad_neighbours (a : Omega) (b : Mathieu23Points a)
    (D : Co3Heptads a) (hb : b ∉ D.val) :
    ((co3ThroughHeptadVectors a b).filter
      (fun y => integerDot (normSixVector a-co3HeptadEndpoint a D).val y.val = 16)).card = 42 := by
  rw [co3ThroughHeptadVectors,Finset.filter_image,
    Finset.card_image_of_injective _ (co3HeptadEndpoint_injective a),Finset.filter_filter]
  have he (B : Co3Heptads a) :
      integerDot (normSixVector a-co3HeptadEndpoint a D).val (co3HeptadEndpoint a B).val = 16 ↔
      (D.val ∩ B.val).card = 1 := by
    rw [co3Heptad_complement_dot]
    omega
  simp_rw [he]
  calc
    _ = ((mathieu23Blocks a).filter (fun B => b ∈ B ∧ (D.val ∩ B).card = 1)).card := by
      convert co3_heptad_filter_card a (fun B => b ∈ B ∧ (D.val ∩ B).card = 1) using 1 <;> congr 1 <;> ext B <;> simp [mathieu23Blocks]
    _ = 42 := by
      convert mathieu23_heptad_intersection_one_card a b D.val D.prop hb using 1 <;> congr 1 <;> ext B <;> simp [mathieu23Blocks]

theorem leech_isometry_neighbour_card (g : LeechIsometryGroup) (S : Finset leech)
    (hg : S.image g.val = S) (w : leech) (k : ℤ) :
    (S.filter (fun y => integerDot (g.val w).val y.val = k)).card =
      (S.filter (fun y => integerDot w.val y.val = k)).card := by
  conv_lhs => rw [← hg]
  rw [Finset.filter_image,Finset.card_image_of_injective _ g.val.injective]
  apply congrArg Finset.card
  apply Finset.filter_congr
  intro y hy
  rw [g.prop]

end Atlas.Conway
