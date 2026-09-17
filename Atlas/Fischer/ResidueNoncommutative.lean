import Atlas.Fischer.ResiduePerfectness

noncomputable section
namespace Atlas.Fischer
open Atlas.Codes

theorem residueGroup_nontrivial (S : Finset Omega) (hpos : 0 < S.card) (hS : S.card ≤ 2) :
    Nontrivial (ResidueGroup S) := by
  apply Finite.one_lt_card_iff_nontrivial.mp
  interval_cases hc : S.card
  · rw [residueGroup_singleton_order S hc]
    decide
  · rw [residueGroup_pair_order S hc]
    decide

/-- The nonempty residues are noncommutative, from perfectness and their
independently computed central-quotient orders. -/
theorem residueGroup_noncommutative (S : Finset Omega) (hpos : 0 < S.card) (hS : S.card ≤ 2) :
    ¬ IsMulCommutative (ResidueGroup S) := by
  haveI := residueGroup_nontrivial S hpos hS
  haveI := residueGroup_perfect S hpos hS
  exact Group.IsPerfect.not_isMulCommutative (ResidueGroup S)

end Atlas.Fischer
