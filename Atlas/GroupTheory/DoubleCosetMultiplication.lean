import Mathlib.GroupTheory.DoubleCoset
import Mathlib.Tactic.Group

/-! Elementary double-coset multiplication from an explicit middle-sandwich
condition. No BN-pair, finiteness or generation hypothesis is used. -/
namespace Atlas.GroupTheory
open scoped Pointwise

variable {G : Type*} [Group G]

theorem subgroup_or_doubleCoset_mul_left_right
    (B : Subgroup G) (n : G) {g : G}
    (hg : g ∈ B ∨ g ∈ DoubleCoset.doubleCoset n B B)
    (a c : G) (ha : a ∈ B) (hc : c ∈ B) :
    a * g * c ∈ B ∨ a * g * c ∈ DoubleCoset.doubleCoset n B B := by
  rcases hg with hg | hg
  · exact Or.inl (B.mul_mem (B.mul_mem ha hg) hc)
  · right
    obtain ⟨x,hx,y,hy,hg⟩ := DoubleCoset.mem_doubleCoset.mp hg
    apply DoubleCoset.mem_doubleCoset.mpr
    refine ⟨a*x,B.mul_mem ha hx,y*c,B.mul_mem hy hc,?_⟩
    rw [hg]
    group

/-- Multiplying the simple double coset by itself reduces to its middle
factor n*b*n. The hypothesis is a concrete containment, not a BN axiom. -/
theorem doubleCoset_mul_self_subset_of_sandwich
    (B : Subgroup G) (n : G)
    (hsandwich : ∀ g ∈ B,
      n * g * n ∈ B ∨ n * g * n ∈ DoubleCoset.doubleCoset n B B) :
    DoubleCoset.doubleCoset n B B * DoubleCoset.doubleCoset n B B ⊆
      (B : Set G) ∪ DoubleCoset.doubleCoset n B B := by
  rintro g ⟨x,hx,y,hy,rfl⟩
  obtain ⟨a,ha,b,hb,hx⟩ := DoubleCoset.mem_doubleCoset.mp hx
  obtain ⟨c,hc,d,hd,hy⟩ := DoubleCoset.mem_doubleCoset.mp hy
  have h := subgroup_or_doubleCoset_mul_left_right B n
    (hsandwich (b*c) (B.mul_mem hb hc)) a d ha hd
  have he : x*y = a*(n*(b*c)*n)*d := by
    rw [hx,hy]
    group
  change x*y ∈ B ∨ x*y ∈ DoubleCoset.doubleCoset n B B
  rw [he]
  exact h

end Atlas.GroupTheory
