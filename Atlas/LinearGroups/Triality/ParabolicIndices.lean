import Atlas.LinearGroups.Triality.Order
import Atlas.LinearGroups.Triality.ParabolicAction
import Atlas.LinearGroups.Triality.ParabolicOrder

/-! Exact cardinalities of the two parabolic coset spaces, without a claim of
 generalized-hexagon incidence axioms. -/
noncomputable section
namespace Atlas.Triality
open Atlas.Orthogonal
variable (F K : Type*) [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]
variable (hdeg : Module.finrank F K = 3)

theorem card_parabolicPoints : Nat.card (ParabolicPoints F K hdeg) =
    (Nat.card F^3+1)*(Nat.card F^8+Nat.card F^4+1) := by
  have hh := (parabolic F K hdeg).index_mul_card
  change Nat.card (ParabolicPoints F K hdeg)*Nat.card (parabolic F K hdeg)=Nat.card (Group F K) at hh
  have hc : Nat.card (parabolic F K hdeg)=Nat.card (longParabolic F K hdeg) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (longParabolic_le_generated F K hdeg)).toEquiv
  rw [hc] at hh
  apply Nat.eq_of_mul_eq_mul_right (show 0 < Nat.card (longParabolic F K hdeg) from Nat.card_pos)
  rw [hh,card_group_bruhat_sum F K hdeg,weyl_weighted_sum,card_longParabolic_factored F K hdeg]
  ring

theorem card_shortParabolicQuotient :
    Nat.card (Group F K ⧸ (shortParabolic F K hdeg).subgroupOf (generated F K)) =
      (Nat.card F+1)*(Nat.card F^8+Nat.card F^4+1) := by
  have hh := ((shortParabolic F K hdeg).subgroupOf (generated F K)).index_mul_card
  change Nat.card (Group F K ⧸ (shortParabolic F K hdeg).subgroupOf (generated F K))*_=Nat.card (Group F K) at hh
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (shortParabolic_le_generated F K hdeg)).toEquiv] at hh
  apply Nat.eq_of_mul_eq_mul_right (show 0 < Nat.card (shortParabolic F K hdeg) from Nat.card_pos)
  rw [hh,card_group_bruhat_sum F K hdeg,weyl_weighted_sum,card_shortParabolic_factored F K hdeg]
  ring

end Atlas.Triality
