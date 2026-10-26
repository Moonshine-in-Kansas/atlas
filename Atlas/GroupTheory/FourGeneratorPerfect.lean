import Mathlib.GroupTheory.IsPerfect
import Mathlib.GroupTheory.Abelianization.Defs

/-! An elementary perfectness criterion from four short generator relations. -/
namespace Atlas.GroupTheory

/-- These short relations kill the four generators in every abelian quotient. -/
theorem four_generator_perfect {G : Type*} [Group G] (p q r s : G)
    (hgen : Subgroup.closure {p,q,r,s} = ⊤)
    (hqp : q*p = p^2*q) (hrp : (r*p)^7 = 1)
    (hsr : (s*r)^5 = 1) (hword : (p*q*s*r)^7 = 1)
    (hq : q^3 = 1) (hr : r^2 = 1) (hs : s^2 = 1) : Group.IsPerfect G := by
  let f : G →* Abelianization G := Abelianization.of
  have hp1 : f p = 1 := by
    have he : f p * f q = f p ^ 2 * f q := by
      simpa only [map_mul, map_pow, mul_comm (f q) (f p)] using congrArg f hqp
    have he2 : f p * 1 = f p * f p := by
      simpa only [mul_one, pow_two] using mul_right_cancel he
    exact (mul_left_cancel he2).symm
  have hr2 : f r ^ 2 = 1 := by simpa only [map_pow, map_one] using congrArg f hr
  have hr1 : f r = 1 := by
    have he : f r ^ 7 = 1 := by
      simpa only [map_mul, map_pow, map_one, hp1, mul_one] using congrArg f hrp
    rw [show (7 : ℕ) = 2*3+1 from rfl, pow_add, pow_mul, hr2] at he
    simpa using he
  have hs2 : f s ^ 2 = 1 := by simpa only [map_pow, map_one] using congrArg f hs
  have hs1 : f s = 1 := by
    have he : f s ^ 5 = 1 := by
      simpa only [map_mul, map_pow, map_one, hr1, mul_one] using congrArg f hsr
    rw [show (5 : ℕ) = 2*2+1 from rfl, pow_add, pow_mul, hs2] at he
    simpa using he
  have hq3 : f q ^ 3 = 1 := by simpa only [map_pow, map_one] using congrArg f hq
  have hq1 : f q = 1 := by
    have he : f q ^ 7 = 1 := by
      simpa only [map_mul, map_pow, map_one, hp1, hr1, hs1, mul_one, one_mul]
        using congrArg f hword
    rw [show (7 : ℕ) = 3*2+1 from rfl, pow_add, pow_mul, hq3] at he
    simpa using he
  have hker : Subgroup.closure {p,q,r,s} ≤ f.ker := by
    apply (Subgroup.closure_le f.ker).mpr
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl | rfl
    · exact hp1
    · exact hq1
    · exact hr1
    · exact hs1
  rw [hgen] at hker
  refine ⟨?_⟩
  rw [← Abelianization.ker_of]
  exact top_unique hker

end Atlas.GroupTheory
