import Atlas.Comparisons.Exceptional.G2Binary.Derived
import Atlas.GroupTheory.PerfectNormalClosureIwasawa
import Atlas.GroupTheory.IndexTwoNonsquareSimplicity

namespace Atlas.G2.BinaryException

/-- Minimal normality comes from the original 63-point primitive action. -/
theorem H_minimal_normal (L : Subgroup (Model K)) (hL : L.Normal) : L = ⊥ ∨ H ≤ L := by
  by_cases hb : L = ⊥
  · exact Or.inl hb
  · letI := hL
    letI := singularPoints_primitive (K := K)
    letI : Group.IsPerfect (Subgroup.normalClosure (longRootLocal (F := K) : Set (Model K))) :=
      longRootNormalClosure_perfect (F := K)
    exact Or.inr (Atlas.GroupTheory.perfect_normalClosure_minimal
      firstPoint longRootLocal longRootLocal_le_pointStabilizer
      longRootLocal_normal_in_pointStabilizer longRootLocal_commutative L hb)

/-- The literal long-root normal closure is simple, independently of PSU3(3). -/
theorem H_simple : IsSimpleGroup H := by
  letI : Nontrivial H := H.nontrivial_iff_ne_bot.mpr H_ne_bot
  apply Atlas.GroupTheory.simple_of_index_two_minimal_normal_nonsquare H index_H H_minimal_normal
  intro n he
  rw [card_H] at he
  have hlow : 77 < n := by nlinarith
  have hhigh : n < 78 := by nlinarith
  omega

/-- Simplicity for the literal commutator carrier. -/
theorem commutator_simple : IsSimpleGroup (commutator (Model K)) := by
  rw [commutator_eq_H]
  exact H_simple

end Atlas.G2.BinaryException
