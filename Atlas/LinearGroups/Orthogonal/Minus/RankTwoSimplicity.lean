import Atlas.LinearGroups.Orthogonal.Minus.RankTwoComparison
import Atlas.LinearGroups.PSLFamily

/-! Rank-two minus simplicity comes from the actual PSL comparison.
No simplicity input is used in the comparison or its order proof. -/
noncomputable section
namespace Atlas.Orthogonal.Minus
open Matrix Atlas.FiniteQuadratic
variable {F K : Type*} [Field F] [Field K] [Finite F] [Finite K] [Algebra F K]

theorem quadratic_extension_card_ge_four (hdeg : Module.finrank F K = 2) :
    4 ≤ Nat.card K := by
  rw [card_extension hdeg]
  have h : 1 < Nat.card F := Finite.one_lt_card
  nlinarith

theorem rankTwo_elementary_simple (hdeg : Module.finrank F K = 2) :
    IsSimpleGroup (E hdeg 1) := by
  let := Atlas.psl_simple_rank_two (quadratic_extension_card_ge_four hdeg)
  exact (rankTwoElementaryEquiv hdeg).symm.isSimpleGroup

theorem rankTwo_simple (hdeg : Module.finrank F K = 2) :
    IsSimpleGroup (ProjectiveElementary (form hdeg 1)) := by
  let := Atlas.psl_simple_rank_two (quadratic_extension_card_ge_four hdeg)
  exact (rankTwoProjectiveEquiv hdeg).isSimpleGroup

theorem rankTwo_noncommutative (hdeg : Module.finrank F K = 2) :
    ¬ IsMulCommutative (ProjectiveElementary (form hdeg 1)) := by
  intro h
  apply Atlas.psl_nonabelian_rank_two (quadratic_extension_card_ge_four hdeg)
  apply IsMulCommutative.of_comm
  intro x y
  apply (rankTwoProjectiveEquiv hdeg).symm.injective
  simp only [map_mul]
  exact isMulCommutative_iff.mp h _ _

theorem rankTwo_elementary_noncommutative (hdeg : Module.finrank F K = 2) :
    ¬ IsMulCommutative (E hdeg 1) := by
  intro h
  apply Atlas.psl_nonabelian_rank_two (quadratic_extension_card_ge_four hdeg)
  apply IsMulCommutative.of_comm
  intro x y
  apply (rankTwoElementaryEquiv hdeg).injective
  simp only [map_mul]
  exact isMulCommutative_iff.mp h _ _

theorem rankTwo_center_scalar (hdeg : Module.finrank F K = 2) :
    Subgroup.center (E hdeg 1) = elementaryScalarSubgroup (form hdeg 1) := by
  rw [rankTwo_scalar_bot]
  let := rankTwo_elementary_simple hdeg
  rcases (inferInstance : (Subgroup.center (E hdeg 1)).Normal).eq_bot_or_eq_top with h | h
  · exact h
  · exact False.elim (rankTwo_elementary_noncommutative hdeg (Subgroup.center_eq_top_iff.mp h))

/-- Downstream perfectness of the actual rank-two elementary carrier. -/
theorem rankTwo_elementary_perfect (hdeg : Module.finrank F K = 2) :
    Group.IsPerfect (E hdeg 1) := by
  let := rankTwo_elementary_simple hdeg
  constructor
  rcases (inferInstance : (commutator (E hdeg 1)).Normal).eq_bot_or_eq_top with h | h
  · exact False.elim (rankTwo_elementary_noncommutative hdeg
      ((commutator_eq_bot_iff _).mp h))
  · exact h

end Atlas.Orthogonal.Minus
