import Atlas.Codes.TernaryOrientedSyndromes
set_option maxRecDepth 10000

noncomputable section
namespace Atlas.Codes
attribute [local instance] Classical.propDecidable

theorem ternaryOrientedSyndromes_card : ternaryOrientedSyndromes.card = 165 := by
  have ha : Nat.card TernaryOrientedTriad = 660 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_coe, ternaryOrientedTriads_card]
  have hb := Atlas.Combinatorics.card_le_capacity_mul_image
    ternaryOrientedSyndrome 4 ternaryOrientedSyndrome_fiber_le
  rw [show Finset.univ.image ternaryOrientedSyndrome = ternaryOrientedSyndromes from rfl] at hb
  rw [ha] at hb
  have hd : Disjoint (ternarySingletonSyndromes ∪ ternaryPairSyndromes)
      ternaryOrientedSyndromes := Finset.disjoint_union_left.mpr
    ⟨ternarySingleton_oriented_disjoint, ternaryPair_oriented_disjoint⟩
  have hc := Finset.card_le_univ
    ((ternarySingletonSyndromes ∪ ternaryPairSyndromes) ∪ ternaryOrientedSyndromes)
  rw [Finset.card_union_of_disjoint hd,
    Finset.card_union_of_disjoint ternarySmallSyndromes_disjoint,
    ternarySingletonSyndromes_card, ternaryPairSyndromes_card,
    ← Nat.card_eq_fintype_card, ternaryAffineSyndrome_card] at hc
  omega

/-- The affine syndrome space is exhausted by singletons, negative pairs and
oriented triads, with respective cardinalities twelve, sixty-six and165. -/
theorem ternarySyndrome_partition :
    (ternarySingletonSyndromes ∪ ternaryPairSyndromes) ∪ ternaryOrientedSyndromes =
      Finset.univ := by
  apply Finset.eq_univ_of_card
  rw [Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr
    ⟨ternarySingleton_oriented_disjoint, ternaryPair_oriented_disjoint⟩),
    Finset.card_union_of_disjoint ternarySmallSyndromes_disjoint,
    ternarySingletonSyndromes_card, ternaryPairSyndromes_card,
    ternaryOrientedSyndromes_card, ← Nat.card_eq_fintype_card, ternaryAffineSyndrome_card]

theorem ternaryOrientedSyndrome_fiber_card (c : TernaryAffineSyndrome)
    (hc : c ∈ ternaryOrientedSyndromes) :
    Nat.card {p : TernaryOrientedTriad // ternaryOrientedSyndrome p = c} = 4 := by
  apply Atlas.Combinatorics.fiber_eq_capacity_of_saturation
    ternaryOrientedSyndrome 4 ternaryOrientedSyndrome_fiber_le _ c hc
  rw [show Finset.univ.image ternaryOrientedSyndrome = ternaryOrientedSyndromes from rfl]
  rw [Nat.card_eq_fintype_card, Fintype.card_coe, ternaryOrientedTriads_card,
    ternaryOrientedSyndromes_card]

end Atlas.Codes
