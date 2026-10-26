import Atlas.Tits.Order
import Atlas.Tits.NormalQuotients

/-! The original derived subgroup retains the lattice neighbour action and
its literal inclusion in the completed Rudvalis scalar quotient. -/

namespace Atlas.Tits
open Atlas.Rudvalis

/-- Faithfulness is inherited by restriction of the actual ambient action. -/
theorem model_neighbours_faithful : FaithfulSMul Model Neighbours := inferInstance

/-- Normality and ambient primitivity imply transitivity on the 1755 neighbours. -/
instance model_neighbours_transitive : MulAction.IsPretransitive Model Neighbours := by
  letI : derivedSubgroup.Normal := inferInstanceAs (commutator Ambient).Normal
  exact normal_neighbours_transitive derivedSubgroup derived_ne_bot

/-- The stabilizer is the stabilizer in the actual derived subgroup, at any point. -/
theorem model_neighbour_stabilizer_card (v : Neighbours) :
    Nat.card (MulAction.stabilizer Model v) = 10240 := by
  have h := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup Model v)
  rw [Nat.card_prod,MulAction.orbit_eq_univ,Nat.card_univ,cardNeighbours,card] at h
  omega

theorem embedding_range_card : Nat.card embeddingIntoRudvalis.range = 17971200 := by
  rw [←Nat.card_congr (MonoidHom.ofInjective embeddingIntoRudvalis_injective).toEquiv]
  exact card

/-- This is the index of the literal inclusion, with no recognition from order. -/
theorem embedding_range_index : embeddingIntoRudvalis.range.index = 8120 := by
  have h := embeddingIntoRudvalis.range.card_mul_index
  rw [embedding_range_card,rudvalisGroup_order] at h
  omega

end Atlas.Tits
