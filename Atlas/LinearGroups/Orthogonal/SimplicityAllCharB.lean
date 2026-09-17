import Atlas.LinearGroups.Orthogonal.ProjectiveEvenBSimplicity
import Atlas.LinearGroups.Orthogonal.SimplicityStableB

/-! # One actual projective B carrier in all finite characteristics, stable rank -/
noncomputable section
namespace Atlas.Orthogonal
variable {F : Type*} [Field F] [Finite F]

theorem projectiveB_simple_all_char (n : ℕ) :
    IsSimpleGroup (ProjectiveElementary (formB (n + 3) F)) := by
  by_cases h2 : (2 : F) = 0
  · letI : CharP F 2 := CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero h2
    exact even_projectiveB_simple_stable n
  · exact projectiveElementaryB_simple_stable n h2

theorem projectiveB_noncommutative_all_char (n : ℕ) :
    ¬ IsMulCommutative (ProjectiveElementary (formB (n + 3) F)) := by
  by_cases h2 : (2 : F) = 0
  · letI : CharP F 2 := CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero h2
    apply even_projectiveB_noncommutative
    right
    refine ⟨by omega, ?_⟩
    intro h
    have := congrArg Prod.fst h
    simp only [Prod.fst] at this
    omega
  · exact projectiveElementaryB_noncommutative (n + 1) h2
end Atlas.Orthogonal
