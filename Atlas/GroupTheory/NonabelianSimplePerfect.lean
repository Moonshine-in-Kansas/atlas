import Mathlib.GroupTheory.IsPerfect
import Mathlib.GroupTheory.Subgroup.Simple

namespace Atlas.GroupTheory
open scoped IsMulCommutative

theorem nonabelian_simple_perfect (G : Type*) [Group G] [IsSimpleGroup G]
    (hG : ∃ g h : G, g*h ≠ h*g) : Group.IsPerfect G := by
  constructor
  rcases (inferInstance : (commutator G).Normal).eq_bot_or_eq_top with he | he
  · haveI := (commutator_eq_bot_iff G).mp he
    obtain ⟨g,h,hgh⟩ := hG
    exact (hgh (mul_comm g h)).elim
  · exact he

end Atlas.GroupTheory
